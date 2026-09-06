import unittest

from datalog.errors import SafetyError
from datalog.parser import parse
from datalog.safety import compile_rule, order_body
from datalog.syntax import Aggregate, Compare, Literal


def compile_first(text):
    return compile_rule(parse(text).rules[0])


def body_shapes(text):
    """Describe the compiled body of a rule as readable strings."""
    return [str(literal) for literal in compile_first(text).body]


class TestSafety(unittest.TestCase):
    def test_ground_fact_is_accepted(self):
        self.assertTrue(compile_first("p(a, 1).").is_fact)

    def test_non_ground_fact_is_rejected(self):
        with self.assertRaises(SafetyError) as caught:
            compile_first("p(X).")
        self.assertIn("must be ground", str(caught.exception))

    def test_head_variable_must_be_bound(self):
        with self.assertRaises(SafetyError) as caught:
            compile_first("p(X, Y) :- q(X).")
        self.assertIn("Y", str(caught.exception))

    def test_head_variable_may_come_from_assignment(self):
        self.assertEqual(len(compile_first("p(X, Y) :- q(X), Y = X + 1.").body), 2)

    def test_head_variable_may_come_from_aggregate(self):
        rule = compile_first("p(X, N) :- q(X), N = count { r(X, _) }.")
        self.assertIsInstance(rule.body[1], Aggregate)

    def test_negated_variable_must_occur_positively(self):
        with self.assertRaises(SafetyError):
            compile_first("p(X) :- q(X), not r(Y).")

    def test_anonymous_variable_under_negation_is_allowed(self):
        self.assertEqual(len(compile_first("p(X) :- q(X), not r(X, _).").body), 2)

    def test_anonymous_variable_in_head_is_rejected(self):
        with self.assertRaises(SafetyError) as caught:
            compile_first("p(_) :- q(X).")
        self.assertIn("'_'", str(caught.exception))

    def test_comparison_variables_must_be_bound(self):
        with self.assertRaises(SafetyError):
            compile_first("p(X) :- q(X), X < Y.")

    def test_body_is_reordered_so_filters_run_late(self):
        self.assertEqual(
            body_shapes("p(X, Y) :- X < Y, q(X), r(Y)."),
            ["q(X)", "r(Y)", "X < Y"],
        )

    def test_reordering_keeps_source_order_when_already_runnable(self):
        self.assertEqual(
            body_shapes("p(X, Y) :- q(X), r(Y), X < Y."),
            ["q(X)", "r(Y)", "X < Y"],
        )

    def test_negation_is_scheduled_after_its_binder(self):
        self.assertEqual(
            body_shapes("p(X) :- not r(X), q(X)."),
            ["q(X)", "not r(X)"],
        )

    def test_assignment_chain_is_ordered(self):
        self.assertEqual(
            body_shapes("p(Z) :- Z = Y + 1, Y = X * 2, q(X)."),
            ["q(X)", "Y = (X * 2)", "Z = (Y + 1)"],
        )

    def test_aggregate_runs_after_its_group_key(self):
        self.assertEqual(
            body_shapes("p(X, N) :- N = count { r(X, _) }, q(X)."),
            ["q(X)", "N = count { r(X, _) }"],
        )

    def test_aggregate_bodies_are_ordered_recursively(self):
        rule = compile_first("p(X, N) :- q(X), N = sum V { V > 0, r(X, V) }.")
        inner = rule.body[1].body
        self.assertEqual([str(literal) for literal in inner], ["r(X, V)", "V > 0"])

    def test_variables_in_separate_aggregates_are_independent(self):
        # 'X' is local to each aggregate, not a shared group key.
        rule = compile_first("p(A, B) :- A = min X { s(X) }, B = max X { s(X) }.")
        self.assertEqual(len(rule.body), 2)

    def test_aggregate_result_can_be_a_later_group_key(self):
        rule = compile_first(
            "p(N, M) :- q(Z), N = count { r(Z, _) }, M = sum W { s(N, W) }."
        )
        self.assertEqual([type(b).__name__ for b in rule.body],
                         ["Literal", "Aggregate", "Aggregate"])

    def test_unsatisfiable_ordering_names_the_blocking_variables(self):
        with self.assertRaises(SafetyError) as caught:
            compile_first("p(X) :- q(X), Y < Z, r(X).")
        message = str(caught.exception)
        self.assertIn("Y", message)
        self.assertIn("Z", message)

    def test_order_body_accepts_preexisting_bindings(self):
        body = parse("p(X) :- X < Y.").rules[0].body
        ordered, bound = order_body(body, {"X", "Y"})
        self.assertEqual(len(ordered), 1)
        self.assertIsInstance(ordered[0], Compare)
        self.assertEqual(bound, {"X", "Y"})

    def test_compiled_rule_round_trips_to_text(self):
        rule = compile_first("p(X, Y) :- q(X), r(Y), X < Y.")
        self.assertEqual(str(rule), "p(X, Y) :- q(X), r(Y), X < Y.")
        self.assertEqual(str(compile_first("p(a).")), "p(a).")


if __name__ == "__main__":
    unittest.main()
