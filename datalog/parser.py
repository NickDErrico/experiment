"""Recursive-descent parser for Datalog.

Grammar (roughly)::

    program   := (clause | query)*
    clause    := atom ['.' | ':-' body '.']
    query     := '?-' body '.'
    body      := literal (',' literal)*
    literal   := ('not' | '!') atom
               | var '=' aggregate
               | expr compare_op expr
               | atom
    aggregate := aggop [expr] '{' body '}'
    atom      := ident ['(' term (',' term)* ')']
    term      := var | number | string | symbol
    expr      := term | expr binop expr | '-' expr | '(' expr ')'

Literals are disambiguated by ordered attempts with backtracking, which keeps
the grammar readable at the cost of a little re-scanning.
"""

from __future__ import annotations

from .errors import ParseError
from .lexer import EOF, IDENT, NUMBER, PUNCT, STRING, VAR, tokenize
from .syntax import (
    AGGREGATORS,
    COMPARISONS,
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
)

_ADDITIVE = ("+", "-")
_MULTIPLICATIVE = ("*", "/", "%")


class Parser:
    """Parses a token stream into a :class:`~datalog.syntax.Program`."""

    def __init__(self, tokens, source_name=None):
        self.tokens = tokens
        self.pos = 0
        self.source_name = source_name
        self._anon_counter = 0

    # -- token helpers ----------------------------------------------------

    def peek(self, offset=0):
        index = self.pos + offset
        if index >= len(self.tokens):
            return self.tokens[-1]
        return self.tokens[index]

    def at(self, kind, value=None, offset=0):
        token = self.peek(offset)
        if token.kind != kind:
            return False
        return value is None or token.value == value

    def advance(self):
        token = self.peek()
        if token.kind != EOF:
            self.pos += 1
        return token

    def accept(self, kind, value=None):
        if self.at(kind, value):
            return self.advance()
        return None

    def expect(self, kind, value=None, what=None):
        if self.at(kind, value):
            return self.advance()
        token = self.peek()
        expected = what or (repr(value) if value is not None else kind.lower())
        raise ParseError(
            "expected %s but found %s" % (expected, _describe(token)),
            token.line,
            token.col,
            self.source_name,
        )

    def error(self, message, token=None):
        token = token or self.peek()
        return ParseError(message, token.line, token.col, self.source_name)

    # -- entry points -----------------------------------------------------

    def parse_program(self):
        program = Program()
        while not self.at(EOF):
            if self.at(PUNCT, "?-"):
                program.queries.append(self.parse_query())
            else:
                program.rules.append(self.parse_clause())
        return program

    def parse_query(self):
        token = self.expect(PUNCT, "?-")
        body = self.parse_body()
        self.expect(PUNCT, ".", what="'.' at end of query")
        return Query(tuple(body), token.line)

    def parse_clause(self):
        token = self.peek()
        head = self.parse_atom()
        body = ()
        if self.accept(PUNCT, ":-"):
            body = tuple(self.parse_body())
        self.expect(PUNCT, ".", what="'.' at end of clause")
        return Rule(head, body, token.line)

    def parse_body(self):
        literals = [self.parse_literal()]
        while self.accept(PUNCT, ","):
            literals.append(self.parse_literal())
        return literals

    # -- literals ---------------------------------------------------------

    def parse_literal(self):
        # Negation ------------------------------------------------------
        if self.at(IDENT, "not") or self.at(PUNCT, "!"):
            self.advance()
            return Literal(self.parse_atom(), negated=True)

        start = self.pos

        # Aggregate: VAR '=' aggop ... '{' body '}' ----------------------
        if (
            self.at(VAR)
            and self.at(PUNCT, "=", 1)
            and self.at(IDENT, None, 2)
            and self.peek(2).value in AGGREGATORS
        ):
            try:
                return self.parse_aggregate()
            except ParseError:
                self.pos = start

        # Comparison or assignment ---------------------------------------
        try:
            left = self.parse_expr()
            op_token = self._comparison_op()
            if op_token is not None:
                right = self.parse_expr()
                if op_token == "=":
                    if isinstance(left, Var):
                        return Assign(left, right)
                    if isinstance(right, Var):
                        return Assign(right, left)
                return Compare(op_token, left, right)
        except ParseError:
            pass
        self.pos = start

        # Plain atom ------------------------------------------------------
        return Literal(self.parse_atom(), negated=False)

    def _comparison_op(self):
        token = self.peek()
        if token.kind == PUNCT and token.value in COMPARISONS:
            self.advance()
            return token.value
        return None

    def parse_aggregate(self):
        var_token = self.expect(VAR)
        var = self._make_var(var_token)
        if var.anonymous:
            raise self.error("aggregate result cannot be the anonymous variable", var_token)
        self.expect(PUNCT, "=")
        op_token = self.expect(IDENT, what="an aggregate operator")
        op = op_token.value
        if op not in AGGREGATORS:
            raise self.error("unknown aggregate operator %r" % op, op_token)

        expr = None
        if not self.at(PUNCT, "{"):
            expr = self.parse_expr()
        if op == "count" and expr is not None:
            raise self.error(
                "count takes no expression; write 'count { ... }'", op_token
            )
        if op != "count" and expr is None:
            raise self.error(
                "%s needs an expression, e.g. '%s X { ... }'" % (op, op), op_token
            )

        self.expect(PUNCT, "{", what="'{' to open the aggregate body")
        body = self.parse_body()
        self.expect(PUNCT, "}", what="'}' to close the aggregate body")
        return Aggregate(var, op, expr, tuple(body))

    # -- atoms and terms --------------------------------------------------

    def parse_atom(self):
        token = self.peek()
        if token.kind != IDENT:
            raise self.error("expected a predicate name but found %s" % _describe(token))
        self.advance()
        terms = []
        if self.accept(PUNCT, "("):
            if not self.at(PUNCT, ")"):
                terms.append(self.parse_term())
                while self.accept(PUNCT, ","):
                    terms.append(self.parse_term())
            self.expect(PUNCT, ")", what="')' to close the argument list")
        return Atom(token.value, tuple(terms))

    def parse_term(self):
        token = self.peek()
        if token.kind == VAR:
            self.advance()
            return self._make_var(token)
        if token.kind == NUMBER:
            self.advance()
            return Const(token.value)
        if token.kind == STRING:
            self.advance()
            return Const(token.value)
        if token.kind == IDENT:
            self.advance()
            return Const(token.value)
        if token.kind == PUNCT and token.value in ("-", "+"):
            self.advance()
            number = self.expect(NUMBER, what="a number after the sign")
            value = -number.value if token.value == "-" else number.value
            return Const(value)
        raise self.error("expected a term but found %s" % _describe(token))

    def _make_var(self, token):
        if token.value == "_":
            self._anon_counter += 1
            return Var("_%d" % self._anon_counter, anonymous=True)
        return Var(token.value)

    # -- expressions ------------------------------------------------------

    def parse_expr(self):
        return self._parse_additive()

    def _parse_additive(self):
        node = self._parse_multiplicative()
        while self.peek().kind == PUNCT and self.peek().value in _ADDITIVE:
            op = self.advance().value
            node = BinOp(op, node, self._parse_multiplicative())
        return node

    def _parse_multiplicative(self):
        node = self._parse_unary()
        while self.peek().kind == PUNCT and self.peek().value in _MULTIPLICATIVE:
            op = self.advance().value
            node = BinOp(op, node, self._parse_unary())
        return node

    def _parse_unary(self):
        token = self.peek()
        if token.kind == PUNCT and token.value in ("-", "+"):
            self.advance()
            operand = self._parse_unary()
            if token.value == "-":
                if isinstance(operand, Const) and isinstance(operand.value, (int, float)):
                    return Const(-operand.value)
                return UnaryOp("-", operand)
            return operand
        return self._parse_primary()

    def _parse_primary(self):
        token = self.peek()
        if token.kind == PUNCT and token.value == "(":
            self.advance()
            node = self.parse_expr()
            self.expect(PUNCT, ")", what="')' to close the expression")
            return node
        if token.kind == NUMBER or token.kind == STRING:
            self.advance()
            return Const(token.value)
        if token.kind == VAR:
            self.advance()
            return self._make_var(token)
        if token.kind == IDENT:
            self.advance()
            return Const(token.value)
        raise self.error("expected an expression but found %s" % _describe(token))


def _describe(token):
    if token.kind == EOF:
        return "end of input"
    if token.kind in (IDENT, VAR, PUNCT):
        return repr(token.value)
    return "%s %r" % (token.kind.lower(), token.value)


def parse(text, source_name=None):
    """Parse Datalog source text into a :class:`~datalog.syntax.Program`."""
    return Parser(tokenize(text, source_name), source_name).parse_program()
