"""Bottom-up Datalog evaluation.

The engine evaluates a program stratum by stratum.  Within a stratum it uses
*semi-naive* iteration: after the first round, a rule is only re-fired against
the tuples that were newly derived in the previous round, which avoids
re-deriving the entire relation on every pass.

Values are Python ``str``, ``int`` and ``float``.  Ordering comparisons use a
total order in which all numbers precede all strings, so a heterogeneous
relation can still be sorted and compared without raising.
"""

from __future__ import annotations

import time
from collections import defaultdict

from . import explain, magic
from .errors import DatalogError, EvaluationError, StratificationError
from .parser import parse
from .safety import compile_rule, order_body
from .stratify import stratify
from .syntax import (
    Aggregate,
    Assign,
    Atom,
    BinOp,
    Compare,
    Const,
    Literal,
    Program,
    Query,
    UnaryOp,
    Var,
    format_value,
    literal_vars,
    sort_key,
)

_MISSING = object()
_NO_VALUE = object()

#: Default guard rails.  Pure Datalog always terminates, but arithmetic can
#: manufacture new constants forever (``p(Y) :- p(X), Y = X + 1.``), so we stop
#: with a clear error instead of hanging.
DEFAULT_MAX_TUPLES = 5_000_000
DEFAULT_MAX_ITERATIONS = 100_000


# --------------------------------------------------------------------------
# Relations
# --------------------------------------------------------------------------


class Relation:
    """A set of ground tuples, with lazily built indexes on bound positions."""

    __slots__ = ("name", "arity", "tuples", "rounds", "_version", "_indexes")

    def __init__(self, name, arity, tuples=None):
        self.name = name
        self.arity = arity
        self.tuples = set(tuples) if tuples else set()
        #: ``{tuple: round}`` for the round each tuple was first derived in,
        #: populated only when the engine is tracking derivations.  See
        #: :mod:`datalog.explain` for what the number is good for.
        self.rounds = {}
        self._version = 0
        self._indexes = {}

    @property
    def signature(self):
        return (self.name, self.arity)

    def __len__(self):
        return len(self.tuples)

    def __iter__(self):
        return iter(self.tuples)

    def __contains__(self, tup):
        return tup in self.tuples

    def add(self, tup):
        """Add one tuple; return ``True`` if it was not already present."""
        if tup in self.tuples:
            return False
        self.tuples.add(tup)
        self._version += 1
        return True

    def update(self, tuples):
        """Add many tuples; return the number actually added."""
        before = len(self.tuples)
        self.tuples.update(tuples)
        added = len(self.tuples) - before
        if added:
            self._version += 1
        return added

    def index(self, positions):
        """Return ``{key_tuple: [tuples]}`` grouped by the given positions."""
        positions = tuple(positions)
        cached = self._indexes.get(positions)
        if cached is not None and cached[0] == self._version:
            return cached[1]
        table = {}
        for tup in self.tuples:
            key = tuple(tup[p] for p in positions)
            bucket = table.get(key)
            if bucket is None:
                table[key] = [tup]
            else:
                bucket.append(tup)
        self._indexes[positions] = (self._version, table)
        return table

    def sorted_tuples(self):
        return sorted(self.tuples, key=lambda tup: tuple(sort_key(v) for v in tup))

    def __repr__(self):
        return "<Relation %s/%d: %d tuples>" % (self.name, self.arity, len(self.tuples))


# --------------------------------------------------------------------------
# Query results
# --------------------------------------------------------------------------


class QueryResult:
    """The answers to one query: a variable list plus deduplicated rows."""

    def __init__(self, query, variables, rows, stats=None):
        self.query = query
        self.variables = list(variables)
        self.rows = list(rows)
        #: Statistics for the evaluation that produced these rows, when it was
        #: a demand-driven one with its own fixpoint; ``None`` otherwise.
        self.stats = stats

    @property
    def is_ground(self):
        """True when the query had no variables, so it just succeeds or fails."""
        return not self.variables

    def __bool__(self):
        return bool(self.rows)

    def __len__(self):
        return len(self.rows)

    def __iter__(self):
        for row in self.rows:
            yield dict(zip(self.variables, row))

    def __getitem__(self, item):
        return dict(zip(self.variables, self.rows[item]))

    def as_dicts(self):
        return list(self)

    def __repr__(self):
        return "<QueryResult %s: %d rows>" % (self.query, len(self.rows))


# --------------------------------------------------------------------------
# Engine
# --------------------------------------------------------------------------


class Engine:
    """Loads Datalog rules and evaluates them to a fixpoint.

    >>> engine = Engine()
    >>> _ = engine.load('''
    ...     edge(a, b).  edge(b, c).
    ...     path(X, Y) :- edge(X, Y).
    ...     path(X, Y) :- edge(X, Z), path(Z, Y).
    ... ''')
    >>> sorted(engine.relation('path').tuples)
    [('a', 'b'), ('a', 'c'), ('b', 'c')]
    >>> [row['X'] for row in engine.query('path(a, X)')]
    ['b', 'c']
    """

    def __init__(
        self,
        max_tuples=DEFAULT_MAX_TUPLES,
        max_iterations=DEFAULT_MAX_ITERATIONS,
        track_derivations=False,
    ):
        self.rules = []
        self.relations = {}
        self.strata = []
        self.stratum_of = {}
        self.stats = {}
        self.max_tuples = max_tuples
        self.max_iterations = max_iterations
        #: Record the round each tuple was first derived in, so that
        #: :meth:`explain` can reconstruct proofs.  Off by default: it costs an
        #: integer per tuple, which is only worth paying if you ask.
        self.track_derivations = track_derivations
        self._arity_of = {}
        self._generation = 0
        self._dirty = True

    # -- loading ----------------------------------------------------------

    def load(self, source, source_name=None):
        """Load Datalog text (or a parsed :class:`Program`).

        Queries found in the source are returned as a list of
        :class:`~datalog.syntax.Query` objects rather than run immediately, so
        the caller controls when evaluation happens.
        """
        program = source if isinstance(source, Program) else parse(source, source_name)
        for rule in program.rules:
            self.add_rule(rule)
        return list(program.queries)

    def add_rule(self, rule):
        """Compile and register a single rule or fact."""
        compiled = compile_rule(rule)
        self._check_arity(compiled)
        self.rules.append(compiled)
        self._dirty = True
        return compiled

    def truncate_rules(self, count):
        """Drop every rule after the first ``count``.

        Used by the REPL to roll back a clause that made the program invalid,
        so an interactive session stays usable after a mistake.
        """
        if count >= len(self.rules):
            return
        del self.rules[count:]
        self._arity_of = {}
        for rule in self.rules:
            self._arity_of.setdefault(rule.head.pred, rule.head.arity)
        self._dirty = True

    def reset(self):
        """Forget every rule and derived tuple, keeping the configured limits."""
        self.rules = []
        self.relations = {}
        self.strata = []
        self.stratum_of = {}
        self.stats = {}
        self._arity_of = {}
        self._dirty = True
        return self

    def _check_arity(self, compiled):
        """Reject the same predicate name used with two different arities."""
        name, arity = compiled.head.signature
        previous = self._arity_of.get(name)
        if previous is None:
            self._arity_of[name] = arity
        elif previous != arity:
            raise DatalogError(
                "predicate %s is defined with arity %d and arity %d; a "
                "predicate's arity must be consistent" % (name, previous, arity)
            )

    # -- evaluation -------------------------------------------------------

    def run(self, force=False):
        """Evaluate the program to a fixpoint.  A no-op if already current."""
        if not self._dirty and not force:
            return self
        started = time.perf_counter()

        self.strata, self.stratum_of = stratify(self.rules)
        self.relations = {}
        self._generation = 0
        for signature in self.stratum_of:
            self._relation(signature)

        by_stratum = defaultdict(list)
        for rule in self.rules:
            by_stratum[self.stratum_of[rule.head.signature]].append(rule)

        iterations = 0
        for level in range(len(self.strata)):
            iterations += self._evaluate_stratum(
                by_stratum.get(level, []), self.strata[level]
            )

        self.stats = {
            "strata": len(self.strata),
            "iterations": iterations,
            "rules": len(self.rules),
            "predicates": len(self.relations),
            "tuples": sum(len(rel) for rel in self.relations.values()),
            "seconds": time.perf_counter() - started,
        }
        self._dirty = False
        return self

    def _evaluate_stratum(self, rules, predicates):
        if not rules:
            return 0

        # Round zero: fire every rule once against the current database.
        produced = defaultdict(set)
        for rule in rules:
            self._fire(rule, produced, None, None)
        delta = self._commit(produced)
        iterations = 1

        # Later rounds only need the rules that read from this stratum.
        recursive = []
        for rule in rules:
            positions = [
                position
                for position, literal in enumerate(rule.body)
                if isinstance(literal, Literal)
                and not literal.negated
                and literal.atom.signature in predicates
            ]
            if positions:
                recursive.append((rule, positions))
        if not recursive:
            return iterations

        while any(rel.tuples for rel in delta.values()):
            if iterations >= self.max_iterations:
                raise EvaluationError(
                    "fixpoint not reached after %d iterations; the program is "
                    "probably generating new values through arithmetic"
                    % iterations
                )
            produced = defaultdict(set)
            for rule, positions in recursive:
                for position in positions:
                    source = delta.get(rule.body[position].atom.signature)
                    if source is None or not source.tuples:
                        continue
                    self._fire(rule, produced, position, source)
            delta = self._commit(produced)
            iterations += 1
        return iterations

    def _fire(self, rule, produced, delta_position, delta_relation):
        """Run one rule, collecting head tuples that are not yet known."""
        signature = rule.head.signature
        relation = self._relation(signature)
        known = relation.tuples
        bucket = produced[signature]
        terms = rule.head.terms
        for binding in self._solve(rule.body, 0, {}, delta_position, delta_relation):
            tup = tuple(
                term.value if isinstance(term, Const) else binding[term.name]
                for term in terms
            )
            if tup not in known:
                bucket.add(tup)

    def _commit(self, produced):
        """Move derived tuples into the database; return them as delta relations.

        Every commit opens a new *generation*.  A rule only ever reads tuples
        committed by earlier generations, so the generation a tuple lands in is
        a well-founded measure on derivations — which is exactly what
        :mod:`datalog.explain` needs to walk a proof backwards without looping.
        The counter runs across strata as well as rounds, so it orders the
        whole evaluation and not just one stratum of it.
        """
        delta = {}
        self._generation += 1
        for signature, tuples in produced.items():
            if not tuples:
                continue
            relation = self._relation(signature)
            if self.track_derivations:
                rounds = relation.rounds
                for tup in tuples:
                    rounds.setdefault(tup, self._generation)
            relation.update(tuples)
            delta[signature] = Relation(signature[0], signature[1], tuples)
        if delta and sum(len(r) for r in self.relations.values()) > self.max_tuples:
            raise EvaluationError(
                "derived more than %d tuples; aborting to avoid exhausting "
                "memory" % self.max_tuples
            )
        return delta

    # -- solving ----------------------------------------------------------

    def _solve(self, body, index, binding, delta_position, delta_relation):
        """Yield every extension of ``binding`` that satisfies ``body``."""
        if index == len(body):
            yield binding
            return

        literal = body[index]

        if isinstance(literal, Literal):
            if literal.negated:
                if not self._exists(literal.atom, binding):
                    for result in self._solve(
                        body, index + 1, binding, delta_position, delta_relation
                    ):
                        yield result
                return
            if index == delta_position:
                relation = delta_relation
            else:
                relation = self._relation(literal.atom.signature)
            for extended in self._match(literal.atom, binding, relation):
                for result in self._solve(
                    body, index + 1, extended, delta_position, delta_relation
                ):
                    yield result
            return

        if isinstance(literal, Compare):
            left = self._eval(literal.left, binding)
            right = self._eval(literal.right, binding)
            if compare_values(literal.op, left, right):
                for result in self._solve(
                    body, index + 1, binding, delta_position, delta_relation
                ):
                    yield result
            return

        if isinstance(literal, Assign):
            name = literal.var.name
            if name not in binding:
                extended = dict(binding)
                extended[name] = self._eval(literal.expr, binding)
            elif isinstance(literal.expr, Var) and literal.expr.name not in binding:
                extended = dict(binding)
                extended[literal.expr.name] = binding[name]
            else:
                if binding[name] != self._eval(literal.expr, binding):
                    return
                extended = binding
            for result in self._solve(
                body, index + 1, extended, delta_position, delta_relation
            ):
                yield result
            return

        if isinstance(literal, Aggregate):
            value = self._aggregate(literal, binding)
            if value is _NO_VALUE:
                return
            name = literal.var.name
            if name in binding:
                if binding[name] != value:
                    return
                extended = binding
            else:
                extended = dict(binding)
                extended[name] = value
            for result in self._solve(
                body, index + 1, extended, delta_position, delta_relation
            ):
                yield result
            return

        raise EvaluationError("unsupported body literal: %r" % (literal,))

    def _match(self, atom, binding, relation):
        """Yield bindings extended by every tuple of ``relation`` matching ``atom``."""
        positions = []
        key = []
        for position, term in enumerate(atom.terms):
            if isinstance(term, Const):
                positions.append(position)
                key.append(term.value)
            elif term.name in binding:
                positions.append(position)
                key.append(binding[term.name])

        if positions:
            candidates = relation.index(tuple(positions)).get(tuple(key))
            if not candidates:
                return
        else:
            candidates = relation.tuples

        terms = atom.terms
        for tup in candidates:
            extended = dict(binding)
            ok = True
            for position, term in enumerate(terms):
                if isinstance(term, Var):
                    value = tup[position]
                    seen = extended.get(term.name, _MISSING)
                    if seen is _MISSING:
                        extended[term.name] = value
                    elif seen != value:
                        ok = False
                        break
            if ok:
                yield extended

    def _exists(self, atom, binding):
        """True if any tuple of ``atom``'s relation matches the current binding."""
        relation = self._relation(atom.signature)
        if not relation.tuples:
            return False
        for _ in self._match(atom, binding, relation):
            return True
        return False

    def _aggregate(self, aggregate, binding):
        """Compute one aggregate value, or ``_NO_VALUE`` if it has no answer."""
        local = sorted(_free_names(aggregate.body) - set(binding))
        seen = set()
        values = []
        for solution in self._solve(aggregate.body, 0, dict(binding), None, None):
            key = tuple(solution.get(name, _MISSING) for name in local)
            if key in seen:
                continue
            seen.add(key)
            if aggregate.expr is not None:
                values.append(self._eval(aggregate.expr, solution))

        op = aggregate.op
        if op == "count":
            return len(seen)
        if op == "sum":
            return _numeric_fold(sum, values, op, default=0)
        # min/max follow the same total order as '<', so they work on strings
        # too; sum/avg genuinely need numbers.
        if op == "min":
            return min(values, key=sort_key) if values else _NO_VALUE
        if op == "max":
            return max(values, key=sort_key) if values else _NO_VALUE
        if op == "avg":
            if not values:
                return _NO_VALUE
            total = _numeric_fold(sum, values, op, default=0)
            return _apply_binop("/", total, len(values))
        raise EvaluationError("unknown aggregate operator %r" % op)

    # -- expressions ------------------------------------------------------

    def _eval(self, expr, binding):
        if isinstance(expr, Const):
            return expr.value
        if isinstance(expr, Var):
            value = binding.get(expr.name, _MISSING)
            if value is _MISSING:
                raise EvaluationError(
                    "variable %s is unbound where a value is required" % expr.name
                )
            return value
        if isinstance(expr, BinOp):
            return _apply_binop(
                expr.op, self._eval(expr.left, binding), self._eval(expr.right, binding)
            )
        if isinstance(expr, UnaryOp):
            value = self._eval(expr.operand, binding)
            if expr.op == "-":
                _require_number(value, "-")
                return -value
            return value
        raise EvaluationError("unsupported expression: %r" % (expr,))

    # -- database access --------------------------------------------------

    def _relation(self, signature):
        relation = self.relations.get(signature)
        if relation is None:
            relation = Relation(signature[0], signature[1])
            self.relations[signature] = relation
        return relation

    def relation(self, name, arity=None):
        """Return the :class:`Relation` for ``name`` (evaluating if needed)."""
        self.run()
        if arity is not None:
            return self._relation((name, arity))
        matches = [rel for sig, rel in self.relations.items() if sig[0] == name]
        if not matches:
            return Relation(name, 0)
        if len(matches) > 1:
            raise DatalogError(
                "predicate %s exists with arities %s; pass arity= to disambiguate"
                % (name, sorted(rel.arity for rel in matches))
            )
        return matches[0]

    def predicates(self):
        """All known predicate signatures, sorted."""
        self.run()
        return sorted(self.relations)

    def undefined_predicates(self):
        """Predicates used in a body but never given a fact or rule.

        These always evaluate to the empty relation, which is legal but is a
        common symptom of a typo, so the CLI surfaces them as warnings.
        """
        defined = {rule.head.signature for rule in self.rules}
        used = set()
        for rule in self.rules:
            _collect_body_signatures(rule.body, used)
        return sorted(used - defined)

    # -- querying ---------------------------------------------------------

    def query(self, goal, source_name=None, demand=False):
        """Answer a query.

        ``goal`` may be a :class:`~datalog.syntax.Query`, a body (sequence of
        literals), or text such as ``"path(a, X)"`` / ``"?- path(a, X)."``.

        With ``demand=True`` the query is answered by the magic-set
        transformation (see :mod:`datalog.magic`): the program is rewritten to
        derive only what this query needs, and evaluated separately, leaving
        this engine's own relations untouched.  The answers are the same either
        way, so a program the transformation cannot handle simply falls back to
        evaluating everything.
        """
        query = _coerce_query(goal, source_name)
        variables = _query_variables(query.body)

        if demand:
            result = self._demand_query(query, variables)
            if result is not None:
                return result

        self.run()
        ordered, _ = order_body(query.body, set(), describe=str(query))

        rows = set()
        for binding in self._solve(tuple(ordered), 0, {}, None, None):
            rows.add(tuple(binding[name] for name in variables))
        return QueryResult(query, variables, _sorted_rows(rows))

    def _demand_query(self, query, variables):
        """Answer ``query`` by magic sets, or return ``None`` to fall back."""
        rules = magic.transform(self.rules, query, variables)
        if rules is None:
            return None

        engine = Engine(max_tuples=self.max_tuples, max_iterations=self.max_iterations)
        for rule in rules:
            engine.add_rule(rule)
        try:
            engine.run()
        except StratificationError:
            # Demand for a negated goal has to be computed before the goal is
            # read, and for some programs no ordering does that.  The original
            # program is stratified, so evaluating all of it still works.
            return None

        answers = engine._relation((magic.GOAL, len(variables)))
        return QueryResult(
            query, variables, _sorted_rows(answers.tuples), stats=engine.stats
        )

    # -- explaining -------------------------------------------------------

    def explain(self, fact, source_name=None):
        """Return a :class:`~datalog.explain.Derivation` of ``fact``.

        ``fact`` is a ground atom, as text (``"path(a, d)"``) or an
        :class:`~datalog.syntax.Atom`.  The result is a proof tree: the rule
        that derived the fact, the premises that rule needed, and so on down to
        the base facts it rests on.  ``None`` means the fact was never derived,
        so there is nothing to explain.

        Proofs need to know the round each tuple was derived in, so the first
        call re-evaluates the program with :attr:`track_derivations` on unless
        it was already set.  Later calls are free.

        >>> engine = Engine()
        >>> _ = engine.load('edge(a, b). edge(b, c).'
        ...                 'path(X, Y) :- edge(X, Y).'
        ...                 'path(X, Y) :- edge(X, Z), path(Z, Y).')
        >>> print(engine.explain('path(a, c)'))
        path(a, c)   by  path(X, Y) :- edge(X, Z), path(Z, Y).
        ├─ edge(a, b)
        └─ path(b, c)   by  path(X, Y) :- edge(X, Y).
           └─ edge(b, c)
        """
        atom = _coerce_atom(fact, source_name)
        if not self.track_derivations:
            self.track_derivations = True
            self._dirty = True
        self.run()
        return explain.prove(self, atom)


# --------------------------------------------------------------------------
# Value helpers
# --------------------------------------------------------------------------


def _sorted_rows(rows):
    """Deduplicated answer rows in the engine's total order."""
    return sorted(set(rows), key=lambda row: tuple(sort_key(v) for v in row))


def compare_values(op, left, right):
    if op == "=":
        return left == right
    if op == "!=":
        return left != right
    a = sort_key(left)
    b = sort_key(right)
    if op == "<":
        return a < b
    if op == "<=":
        return a <= b
    if op == ">":
        return a > b
    if op == ">=":
        return a >= b
    raise EvaluationError("unknown comparison operator %r" % op)


def _apply_binop(op, left, right):
    if op == "+":
        if isinstance(left, str) and isinstance(right, str):
            return left + right
        _require_number(left, op)
        _require_number(right, op)
        return left + right
    _require_number(left, op)
    _require_number(right, op)
    if op == "-":
        return left - right
    if op == "*":
        return left * right
    if op == "/":
        if right == 0:
            raise EvaluationError("division by zero")
        if isinstance(left, int) and isinstance(right, int) and left % right == 0:
            return left // right
        return left / right
    if op == "%":
        if right == 0:
            raise EvaluationError("modulo by zero")
        return left % right
    raise EvaluationError("unknown operator %r" % op)


def _require_number(value, op):
    if isinstance(value, (int, float)) and not isinstance(value, bool):
        return
    raise EvaluationError(
        "operator '%s' needs a number but got %s" % (op, format_value(value))
    )


def _numeric_fold(function, values, op, default=_NO_VALUE):
    if not values:
        return default
    for value in values:
        if not isinstance(value, (int, float)) or isinstance(value, bool):
            raise EvaluationError(
                "%s expects numbers but got %s" % (op, format_value(value))
            )
    return function(values)


def _free_names(body):
    names = set()
    for literal in body:
        literal_vars(literal, names)
    return names


def _collect_body_signatures(body, out):
    for literal in body:
        if isinstance(literal, Literal):
            out.add(literal.atom.signature)
        elif isinstance(literal, Aggregate):
            _collect_body_signatures(literal.body, out)
    return out


def _query_variables(body):
    """Named variables of a query, in order of first appearance.

    Anonymous ``_`` variables are omitted: they exist only to say "any value"
    and reporting them as columns would be noise.
    """
    seen = []
    known = set()
    for literal in body:
        for var in _ordered_vars(literal):
            if var.anonymous or var.name in known:
                continue
            known.add(var.name)
            seen.append(var.name)
    return seen


def _ordered_vars(literal):
    """The :class:`Var` nodes inside one literal, in left-to-right order."""
    found = []

    def walk_expr(expr):
        if isinstance(expr, Var):
            found.append(expr)
        elif isinstance(expr, BinOp):
            walk_expr(expr.left)
            walk_expr(expr.right)
        elif isinstance(expr, UnaryOp):
            walk_expr(expr.operand)

    if isinstance(literal, Literal):
        for term in literal.atom.terms:
            if isinstance(term, Var):
                found.append(term)
    elif isinstance(literal, Compare):
        walk_expr(literal.left)
        walk_expr(literal.right)
    elif isinstance(literal, Assign):
        found.append(literal.var)
        walk_expr(literal.expr)
    elif isinstance(literal, Aggregate):
        found.append(literal.var)
        if literal.expr is not None:
            walk_expr(literal.expr)
        for inner in literal.body:
            found.extend(_ordered_vars(inner))
    return found


def _coerce_query(goal, source_name=None):
    if isinstance(goal, Query):
        return goal
    if isinstance(goal, str):
        text = goal.strip()
        if not text.startswith("?-"):
            text = "?- " + text
        if not text.endswith("."):
            text += "."
        program = parse(text, source_name)
        if len(program.queries) != 1 or program.rules:
            raise DatalogError("expected exactly one query, got %r" % goal)
        return program.queries[0]
    return Query(tuple(goal))


def _coerce_atom(fact, source_name=None):
    """Read ``fact`` as a single ground atom, however it was written."""
    if isinstance(fact, Atom):
        atom = fact
    elif isinstance(fact, Literal):
        if fact.negated:
            raise DatalogError("cannot explain a negated literal: %s" % fact)
        atom = fact.atom
    elif isinstance(fact, str):
        text = fact.strip()
        if text.startswith("?-"):
            text = text[2:].strip()
        if not text.endswith("."):
            text += "."
        program = parse(text, source_name)
        if program.queries or len(program.rules) != 1 or program.rules[0].body:
            raise DatalogError("expected exactly one fact, got %r" % fact)
        atom = program.rules[0].head
    else:
        raise DatalogError("cannot explain %r" % (fact,))
    explain.ground_tuple(atom)  # raises with a useful message if it is not ground
    return atom


# --------------------------------------------------------------------------
# Convenience
# --------------------------------------------------------------------------


def solve(source, source_name=None, demand=False):
    """Parse and evaluate ``source``; return ``(engine, results)``.

    ``results`` pairs each ``?-`` query in the source with its
    :class:`QueryResult`.  With ``demand=True`` each query is answered
    demand-driven, and the engine is left unevaluated unless a query falls back.
    """
    engine = Engine()
    queries = engine.load(source, source_name)
    if not demand:
        engine.run()
    return engine, [(query, engine.query(query, demand=demand)) for query in queries]
