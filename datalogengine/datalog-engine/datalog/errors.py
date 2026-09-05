"""Exception types raised by the Datalog engine.

Every error carries a human-readable message; parse errors additionally carry
source coordinates so the CLI can point at the offending character.
"""

from __future__ import annotations


class DatalogError(Exception):
    """Base class for every error raised by this package."""


class ParseError(DatalogError):
    """Raised for lexical and syntactic problems in Datalog source text."""

    def __init__(self, message, line=0, col=0, source_name=None):
        self.message = message
        self.line = line
        self.col = col
        self.source_name = source_name
        where = source_name or "<input>"
        if line:
            super().__init__("%s:%d:%d: %s" % (where, line, col, message))
        else:
            super().__init__("%s: %s" % (where, message))


class SafetyError(DatalogError):
    """Raised when a rule cannot be evaluated safely.

    A rule is *safe* when every variable it needs is guaranteed to be bound to
    finitely many values.  Unsafe rules (``p(X) :- q(Y).``) would have infinite
    answers, so they are rejected at load time rather than at query time.
    """


class StratificationError(DatalogError):
    """Raised when negation or aggregation is used recursively.

    ``p(X) :- q(X), not p(X).`` has no well-defined meaning under the standard
    stratified semantics, so programs like it are rejected.
    """


class EvaluationError(DatalogError):
    """Raised for runtime problems such as type errors in arithmetic."""
