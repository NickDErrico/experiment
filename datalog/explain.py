"""Derivations: why is this fact true?

Bottom-up evaluation answers *what* a program derives.  This module answers
*why* one particular fact was derived, by searching backwards through the
finished database for a rule instance that produces it, and then explaining
that instance's premises the same way.  The result is a proof tree whose leaves
are the base facts the conclusion rests on.

The delicate part of such a search is termination.  ``path(a, b)`` may well be
derivable from ``path(b, a)`` and vice versa, and a naive backward search will
happily walk around that loop forever, or spend exponential time backtracking
out of it.

The engine already computes what is needed to rule that out.  Semi-naive
evaluation proceeds in rounds, and a tuple first committed in round *g* can
only have come from tuples committed strictly before *g*: lower strata are
finished before a stratum begins, and within a stratum each round reads only
what earlier rounds produced.  So the round in which a tuple first appeared is
a well-founded measure on facts.  Recording it costs one integer per tuple and
turns the proof search into a straight descent: a proof of a round-*g* fact
only ever recurses into facts of a strictly smaller round.  No cycle check, no
backtracking blow-up, and -- since within a stratum the measure is exactly the
number of rule applications -- a short proof rather than a rambling one.

Which of several possible derivations you get is chosen deliberately rather
than left to set iteration order, so that explaining the same fact twice prints
the same tree.  See :func:`_prove`.

Tracking is off by default and switched on by :meth:`datalog.Engine.explain`,
which re-evaluates once if it has to.
"""

from __future__ import annotations

from collections import defaultdict
from dataclasses import dataclass, field
from typing import Tuple

from .errors import DatalogError
from .syntax import (
    Aggregate,
    Assign,
    Atom,
    BinOp,
    Compare,
    Const,
    Literal,
    UnaryOp,
    Var,
    sort_key,
)

_MISSING = object()


# --------------------------------------------------------------------------
# The proof tree
# --------------------------------------------------------------------------


@dataclass(frozen=True)
class Condition:
    """A body literal that held without deriving anything.

    Comparisons, assignments, aggregates and satisfied negations all support a
    derivation without themselves being derived, so they are leaves.  The
    literal is stored with the rule's bindings substituted in, which is what
    makes it readable: ``A >= 18`` is a rule, ``20 >= 18`` is a reason.
    """

    literal: object
    note: str = ""

    def __str__(self):
        return str(self.literal) + (("   " + self.note) if self.note else "")


@dataclass(frozen=True)
class Derivation:
    """Why one ground fact holds.

    ``rule`` is the rule that derived it and ``premises`` are that rule's body
    literals under the bindings used: a :class:`Derivation` for each positive
    atom, a :class:`Condition` for everything else.  A base fact has an empty
    body, so it has no premises and is a leaf.
    """

    atom: Atom
    rule: object
    binding: dict = field(default_factory=dict, repr=False)
    premises: Tuple[object, ...] = ()

    @property
    def is_fact(self):
        """True when this node is a base fact rather than a derived one."""
        return not self.rule.body

    @property
    def depth(self):
        """Length of the longest chain of rule applications below this node."""
        if self.is_fact:
            return 0
        below = [p.depth for p in self.premises if isinstance(p, Derivation)]
        return 1 + max(below, default=0)

    def support(self):
        """The base facts this derivation rests on, sorted and deduplicated.

        The answer to "which of my inputs actually mattered here?" — the part
        of the database that would have to change for the conclusion to go
        away by this route.
        """
        found = set()
        _collect_support(self, found)
        return sorted(found, key=str)

    def rules_used(self):
        """The non-fact rules appearing in this derivation, in source order."""
        found = {}
        _collect_rules(self, found)
        return [found[key] for key in sorted(found)]

    def walk(self):
        """Yield every node of the tree, parents before children."""
        yield self
        for premise in self.premises:
            if isinstance(premise, Derivation):
                for node in premise.walk():
                    yield node
            else:
                yield premise

    def to_dict(self):
        """A JSON-friendly view of the tree."""
        if self.is_fact:
            return {"fact": str(self.atom)}
        return {
            "fact": str(self.atom),
            "rule": str(self.rule),
            "line": self.rule.line,
            "premises": [
                premise.to_dict()
                if isinstance(premise, Derivation)
                else {"condition": str(premise.literal), "note": premise.note}
                for premise in self.premises
            ],
        }

    def __str__(self):
        return render(self)


def _collect_support(node, out):
    if node.is_fact:
        out.add(node.atom)
        return
    for premise in node.premises:
        if isinstance(premise, Derivation):
            _collect_support(premise, out)


def _collect_rules(node, out):
    if not node.is_fact:
        out[(node.rule.line, str(node.rule))] = node.rule
    for premise in node.premises:
        if isinstance(premise, Derivation):
            _collect_rules(premise, out)


# --------------------------------------------------------------------------
# Rendering
# --------------------------------------------------------------------------


def render(node):
    """Draw a derivation as an indented tree.

    A derived fact carries the rule that produced it; a base fact stands alone,
    so the two are told apart at a glance.
    """
    lines = []
    _render(node, "", "", lines)
    return "\n".join(lines)


def _render(node, prefix, connector, lines):
    lines.append(prefix + connector + _headline(node))
    if not isinstance(node, Derivation) or not node.premises:
        return
    if not connector:
        child_prefix = prefix  # the root sits flush left
    else:
        child_prefix = prefix + ("   " if connector.startswith("└") else "│  ")
    last = len(node.premises) - 1
    for position, premise in enumerate(node.premises):
        _render(
            premise,
            child_prefix,
            "└─ " if position == last else "├─ ",
            lines,
        )


def _headline(node):
    if isinstance(node, Condition):
        return str(node)
    if node.is_fact:
        return str(node.atom)
    return "%s   by  %s" % (node.atom, node.rule)


# --------------------------------------------------------------------------
# The search
# --------------------------------------------------------------------------


def prove(engine, atom):
    """Return a :class:`Derivation` of ground ``atom``, or ``None``.

    ``None`` means the fact is simply not in the database — it was never
    derived, so there is nothing to explain.
    """
    signature = atom.signature
    relation = engine.relations.get(signature)
    tup = ground_tuple(atom)
    if relation is None or tup not in relation.tuples:
        return None
    round_of = relation.rounds.get(tup)
    if round_of is None:
        raise DatalogError(
            "derivations were not recorded for this evaluation; use "
            "Engine.explain(), or Engine(track_derivations=True)"
        )
    return _prove(engine, _rules_by_head(engine), signature, tup, round_of)


def _rules_by_head(engine):
    """Rules grouped by head signature, base facts first.

    Trying facts before rules means a fact that is also derivable is explained
    as what it is — given — rather than by a rule that happens to re-derive it.
    """
    grouped = defaultdict(list)
    for rule in engine.rules:
        grouped[rule.head.signature].append(rule)
    for rules in grouped.values():
        rules.sort(key=lambda rule: bool(rule.body))
    return grouped


def _prove(engine, grouped, signature, tup, limit):
    """Find a derivation of ``tup`` using only facts from rounds below ``limit``.

    A fact often has several derivations, and which one a search stumbles on
    first depends on the iteration order of a set — which is to say, on the
    process's hash seed.  A debugging tool whose output changes between runs is
    not much of a debugging tool, so this picks a canonical one instead: the
    first rule that can derive the fact at all, and within that rule the
    smallest set of premises in the engine's total order.
    """
    for rule in grouped.get(signature, ()):
        binding = _unify_head(rule.head, tup)
        if binding is None:
            continue
        best = None
        for solution in engine._solve(rule.body, 0, binding, None, None):
            supports = _supporting_tuples(engine, rule, solution, limit)
            if supports is None:
                continue
            key = _premise_key(supports)
            if best is None or key < best[0]:
                best = (key, dict(solution), supports)
        if best is not None:
            _, solution, supports = best
            return Derivation(
                atom=_atom_of(signature, tup),
                rule=rule,
                binding=solution,
                premises=_premises(engine, grouped, rule, solution, supports),
            )
    # Unreachable: the tuple is in the database, so some rule derived it, and
    # the round bound is exactly the one that derivation respected.
    raise DatalogError(
        "internal error: %s is in the database but no rule derives it"
        % (_atom_of(signature, tup),)
    )


def _premise_key(supports):
    """Order candidate premise sets so the choice between them is repeatable."""
    return tuple(
        tuple(sort_key(value) for value in tup) for _, tup, _ in supports
    )


def _supporting_tuples(engine, rule, solution, limit):
    """The positive body facts of one solution, or ``None`` if it is circular.

    A solution is usable only when every fact it reads was derived strictly
    before the fact being explained.  That is what stops the search from
    proving ``path(a, b)`` from itself.
    """
    supports = []
    for literal in rule.body:
        if not isinstance(literal, Literal) or literal.negated:
            continue
        signature = literal.atom.signature
        tup = _instantiate(literal.atom, solution)
        round_of = engine._relation(signature).rounds.get(tup)
        if round_of is None or round_of >= limit:
            return None
        supports.append((signature, tup, round_of))
    return supports


def _premises(engine, grouped, rule, solution, supports):
    """Explain each body literal: a subproof for atoms, a condition otherwise."""
    premises = []
    position = 0
    for literal in rule.body:
        if isinstance(literal, Literal) and not literal.negated:
            signature, tup, round_of = supports[position]
            position += 1
            premises.append(_prove(engine, grouped, signature, tup, round_of))
        else:
            premises.append(_condition(literal, solution))
    return tuple(premises)


def _condition(literal, solution):
    if isinstance(literal, Literal):  # negated: it held by finding nothing
        return Condition(substitute(literal, solution), "(no such fact)")
    return Condition(substitute(literal, solution))


# --------------------------------------------------------------------------
# Instantiation
# --------------------------------------------------------------------------


def ground_tuple(atom):
    """The tuple of an atom whose terms are all constants."""
    values = []
    for term in atom.terms:
        if not isinstance(term, Const):
            raise DatalogError(
                "explain needs a ground fact, but %s contains the variable %s; "
                "query for the answers first, then explain one of them"
                % (atom, term)
            )
        values.append(term.value)
    return tuple(values)


def _atom_of(signature, tup):
    return Atom(signature[0], tuple(Const(value) for value in tup))


def _instantiate(atom, binding):
    return tuple(
        term.value if isinstance(term, Const) else binding[term.name]
        for term in atom.terms
    )


def _unify_head(head, tup):
    """Bindings that make ``head`` equal ``tup``, or ``None`` if none do."""
    binding = {}
    for term, value in zip(head.terms, tup):
        if isinstance(term, Const):
            if term.value != value:
                return None
            continue
        seen = binding.get(term.name, _MISSING)
        if seen is _MISSING:
            binding[term.name] = value
        elif seen != value:
            return None
    return binding


def substitute(node, binding):
    """Replace bound variables in a literal or expression with their values.

    Anonymous variables are left as ``_``: they stand for "anything", and
    printing the particular value that happened to match would suggest the rule
    cared about it.  Variables local to an aggregate are left alone too, since
    the aggregate ranges over them rather than fixing one value.
    """
    if isinstance(node, Var):
        if node.anonymous:
            return node
        value = binding.get(node.name, _MISSING)
        return node if value is _MISSING else Const(value)
    if isinstance(node, Const):
        return node
    if isinstance(node, BinOp):
        return BinOp(
            node.op, substitute(node.left, binding), substitute(node.right, binding)
        )
    if isinstance(node, UnaryOp):
        return UnaryOp(node.op, substitute(node.operand, binding))
    if isinstance(node, Atom):
        return Atom(node.pred, tuple(substitute(term, binding) for term in node.terms))
    if isinstance(node, Literal):
        return Literal(substitute(node.atom, binding), node.negated)
    if isinstance(node, Compare):
        return Compare(
            node.op, substitute(node.left, binding), substitute(node.right, binding)
        )
    if isinstance(node, Assign):
        return Assign(
            substitute(node.var, binding), substitute(node.expr, binding)
        )
    if isinstance(node, Aggregate):
        return Aggregate(
            substitute(node.var, binding),
            node.op,
            node.expr,
            tuple(substitute(inner, binding) for inner in node.body),
        )
    return node


__all__ = [
    "Condition",
    "Derivation",
    "ground_tuple",
    "prove",
    "render",
    "substitute",
]
