"""Safety checking and body reordering.

A Datalog rule is *safe* when every variable it binds ranges over finitely many
values.  Concretely:

* every variable in the head must be bound by a positive body atom, an
  assignment, or an aggregate;
* every variable in a negated atom must also occur positively (``_`` is exempt,
  since an anonymous variable is purely existential);
* every variable used in a comparison or on the right of an assignment must be
  bound before that literal runs.

Rather than force the user to write literals in a runnable order, we reorder
each body: repeatedly emit the first remaining literal whose inputs are already
bound.  If no literal can run, the rule is unsafe and we say which variables
are to blame.
"""

from __future__ import annotations

from dataclasses import dataclass, field
from typing import Tuple

from .errors import SafetyError
from .syntax import (
    Aggregate,
    Assign,
    Atom,
    Compare,
    Literal,
    Var,
    atom_vars,
    expr_vars,
    literal_vars,
)


@dataclass(frozen=True)
class CompiledRule:
    """A rule whose body has been validated and put into execution order."""

    head: Atom
    body: Tuple[object, ...]
    line: int = 0
    source: object = None
    #: Cache for :meth:`delta_body`, keyed by position.  Excluded from equality
    #: and hashing: it is derived from ``body``, not part of the rule's identity.
    _delta_bodies: dict = field(default_factory=dict, compare=False, repr=False)

    @property
    def is_fact(self):
        return not self.body

    def delta_body(self, position):
        """``body`` reordered to start from the literal at ``position``.

        Semi-naive evaluation re-fires a rule against only the tuples derived
        in the previous round, and leaving the body in its compiled order makes
        that join read the wrong way round.  For ``p(X, Y) :- e(X, Z), p(Z, Y).``
        with a delta on ``p``, every round scans the whole of ``e`` and only
        then looks the delta up — so each round costs the size of the database
        no matter how small the delta is.  Driving the join from the delta
        instead turns the round into a handful of index lookups.

        Reordering a conjunction cannot change which tuples satisfy it, so this
        derives exactly the same facts in exactly the same rounds.
        """
        cached = self._delta_bodies.get(position)
        if cached is None:
            ordered, _ = order_body(self.body, set(), first=position)
            cached = tuple(ordered)
            self._delta_bodies[position] = cached
        return cached

    def __str__(self):
        if self.is_fact:
            return "%s." % (self.head,)
        return "%s :- %s." % (self.head, ", ".join(str(b) for b in self.body))


def compile_rule(rule):
    """Validate ``rule`` and return a :class:`CompiledRule`.

    Raises :class:`~datalog.errors.SafetyError` if the rule cannot be evaluated.
    """
    _reject_anonymous_head(rule)

    if not rule.body:
        unbound = atom_vars(rule.head)
        if unbound:
            raise SafetyError(
                "%s (line %d): a fact must be ground, but %s %s unbound"
                % (rule.head, rule.line, _names(unbound), _verb(unbound))
            )
        return CompiledRule(rule.head, (), rule.line, rule)

    ordered, bound = order_body(rule.body, set(), describe=str(rule.head))

    missing = atom_vars(rule.head) - bound
    if missing:
        raise SafetyError(
            "%s (line %d): head %s %s not bound by any positive literal. "
            "Every head variable must appear in a positive body atom, an "
            "assignment, or an aggregate."
            % (rule.head, rule.line, _names(missing), _verb(missing))
        )
    return CompiledRule(rule.head, tuple(ordered), rule.line, rule)


def order_body(body, bound, describe="query", first=None):
    """Order ``body`` so that every literal runs with its inputs bound.

    ``bound`` is the set of variable names already known on entry.  Returns
    ``(ordered_literals, bound_after)``.  Aggregate sub-bodies are ordered
    recursively once the aggregate's own position is fixed.

    ``first`` pins the literal at that index to the front.  It must be a
    positive atom, which never has inputs to wait for, so pinning one can only
    bind *more* variables earlier and never makes the rest unschedulable.
    """
    bound = set(bound)
    remaining = list(body)
    group_keys = _group_keys(body)
    ordered = []

    if first is not None:
        literal = remaining.pop(first)
        ordered.append(literal)
        bound |= provides(literal, bound)

    while remaining:
        for position, literal in enumerate(remaining):
            if not _missing_inputs(literal, bound, group_keys):
                break
        else:
            raise SafetyError(_stuck_message(remaining, bound, group_keys, describe))

        literal = remaining.pop(position)
        if isinstance(literal, Aggregate):
            inner_bound = bound & _body_vars(literal.body)
            inner, _ = order_body(literal.body, inner_bound, describe=str(literal))
            literal = Aggregate(literal.var, literal.op, literal.expr, tuple(inner))
        ordered.append(literal)
        bound |= provides(literal, bound)

    return ordered, bound


def provides(literal, bound):
    """Variables that become bound once ``literal`` has run."""
    if isinstance(literal, Literal):
        return set() if literal.negated else atom_vars(literal.atom)
    if isinstance(literal, Assign):
        if literal.var.name not in bound:
            return {literal.var.name}
        if isinstance(literal.expr, Var):
            return {literal.expr.name}
        return set()
    if isinstance(literal, Aggregate):
        return {literal.var.name}
    return set()


# --------------------------------------------------------------------------
# Internals
# --------------------------------------------------------------------------


def _body_vars(body):
    """Every variable name occurring anywhere in a list of literals."""
    names = set()
    for literal in body:
        literal_vars(literal, names)
    return names


def _group_keys(body):
    """Map each aggregate in ``body`` to its implicit ``GROUP BY`` variables.

    A variable inside an aggregate is a group key when it is also visible in the
    enclosing scope, so it must be bound before the aggregate runs.  The
    enclosing scope is every *non-aggregate* literal of the body, plus the
    result variables of the other aggregates (which are bound once those
    aggregates have run).

    Crucially, another aggregate's *body* is not part of the enclosing scope:
    each aggregate body is its own scope, so ``A = min X {s(X)}, B = max X
    {s(X)}`` uses two independent local ``X`` variables rather than one shared
    key that nothing could ever bind.
    """
    outer = set()
    for literal in body:
        if isinstance(literal, Aggregate):
            outer.add(literal.var.name)
        else:
            literal_vars(literal, outer)

    keys = {}
    for literal in body:
        if not isinstance(literal, Aggregate):
            continue
        inner = _body_vars(literal.body)
        if literal.expr is not None:
            expr_vars(literal.expr, inner)
        keys[id(literal)] = (inner & outer) - {literal.var.name}
    return keys


def _missing_inputs(literal, bound, group_keys):
    """Variables that must be bound before ``literal`` can run, but are not."""
    if isinstance(literal, Literal):
        if not literal.negated:
            return set()
        needed = {
            term.name
            for term in literal.atom.terms
            if isinstance(term, Var) and not term.anonymous
        }
        return needed - bound
    if isinstance(literal, Compare):
        return (expr_vars(literal.left) | expr_vars(literal.right)) - bound
    if isinstance(literal, Assign):
        needed = expr_vars(literal.expr) - bound
        if not needed:
            return set()
        # ``X = Y`` also runs when X is bound and Y is the free one.
        if literal.var.name in bound and isinstance(literal.expr, Var):
            return set()
        return needed
    if isinstance(literal, Aggregate):
        return group_keys.get(id(literal), set()) - bound
    raise SafetyError("unsupported body literal: %r" % (literal,))


def _reject_anonymous_head(rule):
    for term in rule.head.terms:
        if isinstance(term, Var) and term.anonymous:
            raise SafetyError(
                "%s (line %d): '_' cannot appear in a rule head; give the "
                "variable a name." % (rule.head, rule.line)
            )


def _stuck_message(remaining, bound, group_keys, describe):
    blockers = []
    for literal in remaining:
        missing = _missing_inputs(literal, bound, group_keys)
        if missing:
            blockers.append("%s needs %s" % (literal, _names(missing)))
    detail = "; ".join(blockers) if blockers else "no literal could be scheduled"
    return (
        "%s: cannot order the body safely (%s). Every variable used in a "
        "comparison, a negated atom, or an aggregate's group key must first be "
        "bound by a positive atom." % (describe, detail)
    )


def _names(names):
    ordered = sorted(names)
    if len(ordered) == 1:
        return "variable %s" % ordered[0]
    return "variables %s" % ", ".join(ordered)


def _verb(names):
    return "is" if len(names) == 1 else "are"
