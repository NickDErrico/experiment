"""Abstract syntax for Datalog programs.

The tree is deliberately tiny.  A *term* is a variable or a constant; an *atom*
is a predicate applied to terms; a *rule* is a head atom plus a body of
literals.  Everything is a frozen dataclass so clauses can be hashed and
de-duplicated cheaply.
"""

from __future__ import annotations

import re
from dataclasses import dataclass, field
from typing import Optional, Tuple, Union

# A symbol constant may be printed without quotes when it looks like an
# identifier; anything else is rendered as a quoted string.
_BARE_SYMBOL = re.compile(r"[a-z][A-Za-z0-9_]*\Z")

#: Aggregate operators understood by the engine.
AGGREGATORS = ("count", "sum", "min", "max", "avg")

#: Comparison operators understood by the engine.
COMPARISONS = ("=", "!=", "<", "<=", ">", ">=")


# --------------------------------------------------------------------------
# Terms and expressions
# --------------------------------------------------------------------------


@dataclass(frozen=True)
class Var:
    """A logic variable.  ``anonymous`` marks variables written as ``_``."""

    name: str
    anonymous: bool = False

    def __str__(self):
        return "_" if self.anonymous else self.name


@dataclass(frozen=True)
class Const:
    """A constant: a symbol/string, an integer, or a float."""

    value: object

    def __str__(self):
        return format_value(self.value)


@dataclass(frozen=True)
class BinOp:
    """An arithmetic expression such as ``X + 1``."""

    op: str
    left: "Expr"
    right: "Expr"

    def __str__(self):
        return "(%s %s %s)" % (self.left, self.op, self.right)


@dataclass(frozen=True)
class UnaryOp:
    """A unary arithmetic expression such as ``-X``."""

    op: str
    operand: "Expr"

    def __str__(self):
        return "%s%s" % (self.op, self.operand)


Term = Union[Var, Const]
Expr = Union[Var, Const, BinOp, UnaryOp]


# --------------------------------------------------------------------------
# Atoms and body literals
# --------------------------------------------------------------------------


@dataclass(frozen=True)
class Atom:
    """A predicate applied to a tuple of terms."""

    pred: str
    terms: Tuple[Term, ...] = ()

    @property
    def arity(self):
        return len(self.terms)

    @property
    def signature(self):
        """``(name, arity)`` — predicates are identified by name *and* arity."""
        return (self.pred, len(self.terms))

    def __str__(self):
        if not self.terms:
            return self.pred
        return "%s(%s)" % (self.pred, ", ".join(str(t) for t in self.terms))


@dataclass(frozen=True)
class Literal:
    """A positive or negated atom appearing in a rule body."""

    atom: Atom
    negated: bool = False

    def __str__(self):
        return ("not " + str(self.atom)) if self.negated else str(self.atom)


@dataclass(frozen=True)
class Compare:
    """A comparison between two expressions, e.g. ``X < Y + 1``."""

    op: str
    left: Expr
    right: Expr

    def __str__(self):
        return "%s %s %s" % (self.left, self.op, self.right)


@dataclass(frozen=True)
class Assign:
    """Binds ``var`` to the value of ``expr`` (or compares, if already bound)."""

    var: Var
    expr: Expr

    def __str__(self):
        return "%s = %s" % (self.var, self.expr)


@dataclass(frozen=True)
class Aggregate:
    """``Var = op Expr { body }`` — an aggregate over a nested sub-query.

    Variables shared with the enclosing rule act as an implicit ``GROUP BY``;
    variables local to ``body`` are the ones aggregated over.
    """

    var: Var
    op: str
    expr: Optional[Expr]
    body: Tuple["BodyLit", ...]

    def __str__(self):
        inner = ", ".join(str(literal) for literal in self.body)
        target = (" " + str(self.expr)) if self.expr is not None else ""
        return "%s = %s%s { %s }" % (self.var, self.op, target, inner)


BodyLit = Union[Literal, Compare, Assign, Aggregate]


# --------------------------------------------------------------------------
# Clauses
# --------------------------------------------------------------------------


@dataclass(frozen=True)
class Rule:
    """A rule ``head :- body``.  An empty body makes it a fact."""

    head: Atom
    body: Tuple[BodyLit, ...] = ()
    line: int = 0

    @property
    def is_fact(self):
        return not self.body

    def __str__(self):
        if self.is_fact:
            return "%s." % (self.head,)
        return "%s :- %s." % (self.head, ", ".join(str(b) for b in self.body))


@dataclass(frozen=True)
class Query:
    """A ``?- body.`` goal."""

    body: Tuple[BodyLit, ...]
    line: int = 0

    def __str__(self):
        return "?- %s." % ", ".join(str(b) for b in self.body)


@dataclass
class Program:
    """A parsed program: a list of rules (facts included) and queries."""

    rules: list = field(default_factory=list)
    queries: list = field(default_factory=list)

    def __str__(self):
        parts = [str(r) for r in self.rules] + [str(q) for q in self.queries]
        return "\n".join(parts)


# --------------------------------------------------------------------------
# Helpers
# --------------------------------------------------------------------------


def format_value(value):
    """Render a runtime value using Datalog surface syntax."""
    if isinstance(value, bool):  # guard: bool is a subclass of int
        return "true" if value else "false"
    if isinstance(value, str):
        if _BARE_SYMBOL.match(value):
            return value
        escaped = (
            value.replace("\\", "\\\\")
            .replace('"', '\\"')
            .replace("\n", "\\n")
            .replace("\t", "\\t")
            .replace("\r", "\\r")
        )
        return '"%s"' % escaped
    if isinstance(value, float):
        return repr(value)
    return str(value)


def expr_vars(expr, out=None):
    """Collect the names of the variables occurring in an expression."""
    if out is None:
        out = set()
    if isinstance(expr, Var):
        out.add(expr.name)
    elif isinstance(expr, BinOp):
        expr_vars(expr.left, out)
        expr_vars(expr.right, out)
    elif isinstance(expr, UnaryOp):
        expr_vars(expr.operand, out)
    return out


def atom_vars(atom, out=None):
    """Collect the names of the variables occurring in an atom."""
    if out is None:
        out = set()
    for term in atom.terms:
        if isinstance(term, Var):
            out.add(term.name)
    return out


def literal_vars(literal, out=None):
    """Collect every variable name occurring anywhere in a body literal."""
    if out is None:
        out = set()
    if isinstance(literal, Literal):
        atom_vars(literal.atom, out)
    elif isinstance(literal, Compare):
        expr_vars(literal.left, out)
        expr_vars(literal.right, out)
    elif isinstance(literal, Assign):
        out.add(literal.var.name)
        expr_vars(literal.expr, out)
    elif isinstance(literal, Aggregate):
        out.add(literal.var.name)
        if literal.expr is not None:
            expr_vars(literal.expr, out)
        for inner in literal.body:
            literal_vars(inner, out)
    return out


def body_predicates(body, out=None, negative=None, depth=0):
    """Split the predicates referenced by ``body`` into positive and negative.

    ``negative`` receives predicates reached through negation *or* through an
    aggregate body — both require the callee to be fully evaluated first, so
    both must land in a strictly lower stratum.
    """
    if out is None:
        out = set()
    if negative is None:
        negative = set()
    for literal in body:
        if isinstance(literal, Literal):
            target = negative if (literal.negated or depth > 0) else out
            target.add(literal.atom.signature)
        elif isinstance(literal, Aggregate):
            body_predicates(literal.body, out, negative, depth + 1)
    return out, negative
