"""A small, dependency-free Datalog engine.

Quick start::

    from datalog import Engine

    engine = Engine()
    engine.load('''
        edge(a, b).  edge(b, c).  edge(c, d).
        path(X, Y) :- edge(X, Y).
        path(X, Y) :- edge(X, Z), path(Z, Y).
    ''')
    for row in engine.query('path(a, X)'):
        print(row['X'])

The engine supports recursion, stratified negation, comparisons, arithmetic and
aggregates, and evaluates bottom-up with semi-naive iteration.  A query can also
be answered demand-driven, by the magic-set transformation in
:mod:`datalog.magic`, so that only the facts it needs are derived.
"""

from .engine import Engine, QueryResult, Relation, solve
from .errors import (
    DatalogError,
    EvaluationError,
    ParseError,
    SafetyError,
    StratificationError,
)
from .parser import parse
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
    Rule,
    UnaryOp,
    Var,
    format_value,
)

__version__ = "0.1.0"

__all__ = [
    "Aggregate",
    "Assign",
    "Atom",
    "BinOp",
    "Compare",
    "Const",
    "DatalogError",
    "Engine",
    "EvaluationError",
    "Literal",
    "ParseError",
    "Program",
    "Query",
    "QueryResult",
    "Relation",
    "Rule",
    "SafetyError",
    "StratificationError",
    "UnaryOp",
    "Var",
    "__version__",
    "format_value",
    "parse",
    "solve",
]
