import unittest

from datalog.errors import ParseError
from datalog.parser import parse
from datalog.syntax import (
    Aggregate,
    Assign,
    Atom,
    BinOp,
    Compare,
    Const,
    Literal,
    Var,
)


class TestParser(unittest.TestCase):
    def test_fact(self):
        program = parse("parent(alice, bob).")
        self.assertEqual(len(program.rules), 1)
        rule = program.rules[0]
        self.assertTrue(rule.is_fact)
        self.assertEqual(rule.head, Atom("parent", (Const("alice"), Const("bob"))))

    def test_zero_arity_atom(self):
        program = parse("ready. go :- ready.")
        self.assertEqual(program.rules[0].head, Atom("ready", ()))
        self.assertEqual(program.rules[1].body[0], Literal(Atom("ready", ())))

    def test_rule_and_variables(self):
        rule = parse("p(X, Y) :- q(X, Z), r(Z, Y).").rules[0]
        self.assertEqual(rule.head.terms, (Var("X"), Var("Y")))
        self.assertEqual(len(rule.body), 2)
        self.assertEqual(rule.body[0].atom.pred, "q")

    def test_negation_both_spellings(self):
        for text in ("p(X) :- q(X), not r(X).", "p(X) :- q(X), !r(X)."):
            rule = parse(text).rules[0]
            self.assertTrue(rule.body[1].negated, text)

    def test_anonymous_variables_are_distinct(self):
        rule = parse("p(X) :- q(X, _), r(X, _).").rules[0]
        first = rule.body[0].atom.terms[1]
        second = rule.body[1].atom.terms[1]
        self.assertTrue(first.anonymous and second.anonymous)
        self.assertNotEqual(first.name, second.name)

    def test_comparisons(self):
        rule = parse("p(X) :- q(X), X < 3, X != a, X >= 1.").rules[0]
        operators = [b.op for b in rule.body if isinstance(b, Compare)]
        self.assertEqual(operators, ["<", "!=", ">="])

    def test_assignment_forms(self):
        rule = parse("p(Y) :- q(X), Y = X + 1.").rules[0]
        self.assertIsInstance(rule.body[1], Assign)
        self.assertEqual(rule.body[1].var, Var("Y"))
        # A constant on the left still yields an assignment to the variable.
        rule = parse("p(X) :- q(X), 3 = X.").rules[0]
        self.assertIsInstance(rule.body[1], Assign)
        self.assertEqual(rule.body[1].var, Var("X"))

    def test_arithmetic_precedence(self):
        rule = parse("p(Y) :- q(X), Y = 1 + X * 2.").rules[0]
        expr = rule.body[1].expr
        self.assertEqual(expr.op, "+")
        self.assertIsInstance(expr.right, BinOp)
        self.assertEqual(expr.right.op, "*")

    def test_parenthesised_expression(self):
        rule = parse("p(Y) :- q(X), Y = (1 + X) * 2.").rules[0]
        expr = rule.body[1].expr
        self.assertEqual(expr.op, "*")
        self.assertEqual(expr.left.op, "+")

    def test_negative_number_term(self):
        rule = parse("p(-3).").rules[0]
        self.assertEqual(rule.head.terms[0], Const(-3))

    def test_aggregate(self):
        rule = parse("p(P, N) :- q(P), N = count { r(P, X) }.").rules[0]
        aggregate = rule.body[1]
        self.assertIsInstance(aggregate, Aggregate)
        self.assertEqual(aggregate.op, "count")
        self.assertIsNone(aggregate.expr)
        self.assertEqual(aggregate.var, Var("N"))

    def test_aggregate_with_expression(self):
        rule = parse("p(S) :- S = sum X * 2 { q(X) }.").rules[0]
        aggregate = rule.body[0]
        self.assertEqual(aggregate.op, "sum")
        self.assertIsInstance(aggregate.expr, BinOp)

    def test_count_rejects_expression(self):
        with self.assertRaises(ParseError):
            parse("p(N) :- N = count X { q(X) }.")

    def test_sum_requires_expression(self):
        with self.assertRaises(ParseError):
            parse("p(N) :- N = sum { q(X) }.")

    def test_symbol_named_like_aggregate_still_parses(self):
        # 'count' is only special immediately after '=' and before a '{'.
        rule = parse("p(X) :- q(X), X = count.").rules[0]
        self.assertIsInstance(rule.body[1], Assign)
        self.assertEqual(rule.body[1].expr, Const("count"))

    def test_queries(self):
        program = parse("p(a). ?- p(X). ?- p(X), X != a.")
        self.assertEqual(len(program.queries), 2)
        self.assertEqual(len(program.queries[1].body), 2)

    def test_line_numbers_recorded(self):
        program = parse("p(a).\n\nq(b).")
        self.assertEqual(program.rules[0].line, 1)
        self.assertEqual(program.rules[1].line, 3)

    def test_round_trip_of_str(self):
        text = "p(X, Y) :- q(X, Z), not r(Z), Z < 3, Y = Z + 1."
        rule = parse(text).rules[0]
        self.assertEqual(parse(str(rule)).rules[0], rule)

    def test_parse_errors(self):
        for bad in [
            "p(a)",            # missing period
            "p(a) :- .",       # empty body
            ":- q(a).",        # no head
            "p(a) :- q(.",     # unclosed argument list
            "P(a).",           # head must be a predicate, not a variable
            "p(a) :- N = count { }.",
        ]:
            with self.assertRaises(ParseError, msg=bad):
                parse(bad)

    def test_error_message_mentions_location(self):
        with self.assertRaises(ParseError) as caught:
            parse("p(a).\nq(b)\n", "demo.dl")
        self.assertIn("demo.dl", str(caught.exception))
        self.assertIn("expected", str(caught.exception))


if __name__ == "__main__":
    unittest.main()
