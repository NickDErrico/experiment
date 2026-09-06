"""The magic-set transformation: bottom-up evaluation, driven by the query.

Evaluating a program bottom-up computes *every* fact it can derive.  That is
the right trade when the query is broad, and the wrong one when it is narrow:
asking ``?- path(a, X)`` over a large graph derives the whole transitive
closure, then throws away all but one row's worth of it.

The classical fix is to rewrite the program so that bottom-up evaluation only
derives what the query needs.  For each predicate we invent a *magic* companion
that records which calls are actually demanded, and we guard each rule with it::

    path(X, Y) :- edge(X, Y).                    ?- path(a, W).
    path(X, Y) :- edge(X, Z), path(Z, Y).

becomes (writing ``m_path_bf`` for "path was called with its first argument
bound")::

    m_path_bf(a).                                       // the query is the seed
    path(X, Y) :- m_path_bf(X), edge(X, Y).
    path(X, Y) :- m_path_bf(X), edge(X, Z), path(Z, Y).
    m_path_bf(Z) :- m_path_bf(X), edge(X, Z).           // the demand it creates

The guards make each rule fire only for demanded calls, and the last rule
propagates demand the same way the original rule passes bindings sideways --
so the fixpoint now explores the graph *forwards from* ``a`` rather than
building every path in it.  The answers are unchanged; the work is not.

Two departures from the textbook presentation:

*Adornments name the magic predicates, but not the relations.*  Every adorned
copy of a rule writes into the original predicate, so ``path`` still means
``path`` and the caller can read answers straight out of it.  This is sound
because every derived fact is a fact of the original program either way, and
adding facts derived under one binding pattern can never remove an answer under
another.

*The transformation is optional and may decline.*  Demand for a negated goal
has to be computed before the negated relation is evaluated, and there are
stratified programs whose transformed form has no stratification at all.
:func:`transform` returns ``None`` when it cannot help or cannot be trusted --
aggregates, no bound argument to propagate anywhere, an adornment explosion --
and the caller falls back to evaluating the whole program.  A transformation
that survives :func:`~datalog.stratify.stratify` is one whose negated goals are
fully demanded before they are read.
"""

from __future__ import annotations

from collections import defaultdict

from .safety import order_body, provides
from .syntax import Aggregate, Atom, Const, Literal, Rule, Var

#: Head predicate of the synthesised rule that stands for the query.  The ``#``
#: keeps every name this module invents out of the user's namespace: the lexer
#: cannot produce an identifier containing one.
GOAL = "#goal"

#: Give up rather than generate a specialised copy of a predicate for more than
#: this many binding patterns.
DEFAULT_MAX_ADORNMENTS = 8

#: Give up rather than emit more than this many rules.
DEFAULT_MAX_RULES = 5_000


def magic_name(signature, adornment):
    """Name of the magic companion of ``signature`` under ``adornment``.

    >>> magic_name(("path", 2), "bf")
    '#magic#path/2#bf'
    """
    return "#magic#%s/%d#%s" % (signature[0], signature[1], adornment)


def goal_rule(query, variables):
    """The query, expressed as an ordinary rule deriving :data:`GOAL`."""
    ordered, _ = order_body(query.body, set(), describe=str(query))
    head = Atom(GOAL, tuple(Var(name) for name in variables))
    return Rule(head, tuple(ordered), query.line)


def transform(
    rules,
    query,
    variables,
    max_adornments=DEFAULT_MAX_ADORNMENTS,
    max_rules=DEFAULT_MAX_RULES,
):
    """Rewrite ``rules`` so that evaluating them answers ``query`` and no more.

    ``rules`` are compiled rules, so their bodies are already in the order the
    engine will run them -- which is exactly the order bindings flow sideways
    in.  ``variables`` names the query's answer columns; the transformed
    program derives them as :data:`GOAL` facts.

    Returns a list of :class:`~datalog.syntax.Rule`, or ``None`` if the
    transformation does not apply.
    """
    return _Transformer(rules, max_adornments, max_rules).run(query, variables)


class _Transformer:
    def __init__(self, rules, max_adornments, max_rules):
        self.max_adornments = max_adornments
        self.max_rules = max_rules

        self.rules_of = defaultdict(list)
        for rule in rules:
            self.rules_of[rule.head.signature].append(rule)

        # A predicate is intensional when something *derives* it.  Predicates
        # given only as facts are the extensional database: they are already
        # materialised, so demanding them would only add a join.
        self.derived = {
            signature
            for signature, group in self.rules_of.items()
            if any(not rule.is_fact for rule in group)
        }

        self.out = []
        self.seen = set()
        self.pending = []
        self.adornments_of = defaultdict(set)
        self.base = set()
        self.goal_demands = []

    # -- driver -----------------------------------------------------------

    def run(self, query, variables):
        goal = goal_rule(query, variables)
        goal_signature = goal.head.signature
        self.rules_of[goal_signature] = [goal]
        self.derived.add(goal_signature)

        adornment = "f" * len(variables)
        self._demand(goal_signature, adornment)
        while self.pending:
            if not self._visit(*self.pending.pop()):
                return None
            if len(self.out) > self.max_rules:
                return None

        # If the query itself binds nothing, it is asking for whole relations
        # and the guards would admit everything: no answers saved, one join per
        # rule spent.  Demand a rewrite only when the goal has something to
        # push down.
        if not any("b" in adorned for adorned in self.goal_demands):
            return None

        self.out.append(Rule(Atom(magic_name(goal_signature, adornment), ()), ()))
        for base in sorted(self.base):
            self.out.extend(
                Rule(rule.head, (), rule.line) for rule in self.rules_of[base]
            )
        return self.out

    def _demand(self, signature, adornment):
        if (signature, adornment) in self.seen:
            return True
        self.adornments_of[signature].add(adornment)
        if len(self.adornments_of[signature]) > self.max_adornments:
            return False
        self.seen.add((signature, adornment))
        self.pending.append((signature, adornment))
        return True

    def _visit(self, signature, adornment):
        for rule in self.rules_of[signature]:
            if _has_aggregate(rule.body):
                # Demand would have to be propagated into the aggregate's own
                # scope, and an under-demanded aggregate returns a wrong
                # number rather than fewer rows.  Not worth the risk.
                return False
            if not self._adorn(rule, adornment):
                return False
        return True

    # -- rewriting one rule -----------------------------------------------

    def _adorn(self, rule, adornment):
        """Emit the guarded copy of ``rule``, and the demand its body creates."""
        guard = Literal(_magic_atom(rule.head, adornment))
        bound = _bound_names(rule.head, adornment)
        is_goal = rule.head.pred == GOAL

        prefix = [guard]
        for literal in rule.body:
            if isinstance(literal, Literal):
                signature = literal.atom.signature
                if signature in self.derived:
                    inner = _adornment_of(literal.atom, bound)
                    if is_goal:
                        self.goal_demands.append(inner)
                    self.out.append(
                        Rule(_magic_atom(literal.atom, inner), tuple(prefix), rule.line)
                    )
                    if not self._demand(signature, inner):
                        return False
                elif signature in self.rules_of:
                    self.base.add(signature)
            prefix.append(literal)
            bound |= provides(literal, bound)

        self.out.append(Rule(rule.head, tuple(prefix), rule.line))
        return True


# --------------------------------------------------------------------------
# Internals
# --------------------------------------------------------------------------


def _adornment_of(atom, bound):
    """Which of ``atom``'s arguments are already known when it is reached.

    A constant is bound by definition.  ``_`` never is: it is a fresh variable
    that exists only to be ignored.
    """
    return "".join(
        "b" if _is_bound(term, bound) else "f" for term in atom.terms
    )


def _is_bound(term, bound):
    if isinstance(term, Const):
        return True
    return isinstance(term, Var) and not term.anonymous and term.name in bound


def _magic_atom(atom, adornment):
    """``atom``'s magic companion: the same atom, keeping its bound arguments."""
    terms = tuple(
        term for term, mark in zip(atom.terms, adornment) if mark == "b"
    )
    return Atom(magic_name(atom.signature, adornment), terms)


def _bound_names(atom, adornment):
    return {
        term.name
        for term, mark in zip(atom.terms, adornment)
        if mark == "b" and isinstance(term, Var) and not term.anonymous
    }


def _has_aggregate(body):
    for literal in body:
        if isinstance(literal, Aggregate):
            return True
    return False
