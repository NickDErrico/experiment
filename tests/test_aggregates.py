import unittest

from datalog import Engine
from datalog.errors import EvaluationError


def run(source):
    engine = Engine()
    engine.load(source)
    engine.run()
    return engine


class TestAggregates(unittest.TestCase):
    SALES = """
        person(alice). person(bob). person(carol).
        sale(alice, 10). sale(alice, 20). sale(alice, 20). sale(bob, 5).
    """

    def test_count_groups_by_shared_variables(self):
        engine = run(self.SALES + "n(P, C) :- person(P), C = count { sale(P, _) }.")
        # alice has three sale facts but only two distinct amounts, and the
        # aggregate's local variable is the amount, so distinct amounts win.
        self.assertEqual(
            engine.relation("n").tuples, {("alice", 2), ("bob", 1), ("carol", 0)}
        )

    def test_count_is_distinct_over_all_local_variables(self):
        # '_' is a fresh variable like any other, so it is part of the witness
        # being counted: 'count { r(K, U, _) }' counts distinct (U, _) pairs,
        # not distinct U values.
        engine = run(
            """
            r(a, 1, x). r(a, 1, y). r(a, 2, x).
            k(a).
            pairs(K, N)  :- k(K), N = count { r(K, U, V) }.
            anon(K, N)   :- k(K), N = count { r(K, U, _) }.
            projected(K, N) :- k(K), N = count { first(K, U) }.
            first(K, U)  :- r(K, U, _).
            """
        )
        self.assertEqual(engine.relation("pairs").tuples, {("a", 3)})
        self.assertEqual(engine.relation("anon").tuples, {("a", 3)})
        # To count distinct U values, project first with a helper predicate.
        self.assertEqual(engine.relation("projected").tuples, {("a", 2)})

    def test_sum_min_max_avg(self):
        engine = run(
            """
            s(1). s(2). s(3). s(4).
            stats(Sum, Min, Max, Avg) :-
                Sum = sum X { s(X) },
                Min = min X { s(X) },
                Max = max X { s(X) },
                Avg = avg X { s(X) }.
            """
        )
        self.assertEqual(engine.relation("stats").tuples, {(10, 1, 4, 2.5)})

    def test_average_of_exact_division_is_an_integer(self):
        engine = run("s(2). s(4). avgv(A) :- A = avg X { s(X) }.")
        self.assertEqual(engine.relation("avgv").tuples, {(3,)})

    def test_aggregate_expression_may_be_arithmetic(self):
        engine = run("s(1). s(2). d(T) :- T = sum X * 10 { s(X) }.")
        self.assertEqual(engine.relation("d").tuples, {(30,)})

    def test_sum_of_empty_group_is_zero_but_min_has_no_answer(self):
        engine = run(
            """
            k(a). k(b).
            v(a, 1).
            total(K, S) :- k(K), S = sum X { v(K, X) }.
            lowest(K, M) :- k(K), M = min X { v(K, X) }.
            """
        )
        self.assertEqual(engine.relation("total").tuples, {("a", 1), ("b", 0)})
        self.assertEqual(engine.relation("lowest").tuples, {("a", 1)})

    def test_aggregate_over_a_recursive_relation(self):
        engine = run(
            """
            edge(a, b). edge(b, c). edge(c, d).
            node(X) :- edge(X, _).
            node(Y) :- edge(_, Y).
            path(X, Y) :- edge(X, Y).
            path(X, Y) :- edge(X, Z), path(Z, Y).
            reach(X, N) :- node(X), N = count { path(X, _) }.
            """
        )
        self.assertEqual(
            engine.relation("reach").tuples,
            {("a", 3), ("b", 2), ("c", 1), ("d", 0)},
        )

    def test_nested_aggregates(self):
        engine = run(
            """
            k(a). k(b).
            d(a, 1). d(a, 2). d(b, 3).
            total(T) :- T = sum S { k(P), S = sum V { d(P, V) } }.
            """
        )
        # a sums to 3, b sums to 3; distinctness keys on (P, S), so both count.
        self.assertEqual(engine.relation("total").tuples, {(6,)})

    def test_aggregate_result_used_by_a_later_aggregate(self):
        engine = run(
            """
            q(x). r(x, 1). r(x, 2). s(1, 10). s(2, 20).
            o(N, M) :- q(Z), N = count { r(Z, _) }, M = sum W { s(N, W) }.
            """
        )
        self.assertEqual(engine.relation("o").tuples, {(2, 20)})

    def test_aggregate_result_can_be_filtered(self):
        engine = run(
            """
            k(a). k(b).
            v(a, 1). v(a, 2). v(b, 1).
            busy(K) :- k(K), N = count { v(K, _) }, N > 1.
            """
        )
        self.assertEqual(engine.relation("busy").tuples, {("a",)})

    def test_aggregate_result_compared_against_a_bound_value(self):
        engine = run("k(a, 2). v(a, 1). v(a, 5). match(K) :- k(K, N), N = count { v(K, _) }.")
        self.assertEqual(engine.relation("match").tuples, {("a",)})

    def test_global_aggregate_with_no_group_key(self):
        engine = run("s(1). s(2). s(3). total(T) :- T = sum X { s(X) }.")
        self.assertEqual(engine.relation("total").tuples, {(6,)})

    def test_aggregate_over_a_negated_body(self):
        engine = run(
            """
            n(a). n(b). n(c).
            flagged(b).
            clean(N) :- N = count { n(X), not flagged(X) }.
            """
        )
        self.assertEqual(engine.relation("clean").tuples, {(2,)})

    def test_non_numeric_aggregate_is_an_error(self):
        engine = Engine()
        engine.load("s(a). s(b). total(T) :- T = sum X { s(X) }.")
        with self.assertRaises(EvaluationError) as caught:
            engine.run()
        self.assertIn("sum", str(caught.exception))

    def test_min_and_max_use_the_total_order(self):
        engine = run('s(1). s("a"). lo(M) :- M = min X { s(X) }. hi(M) :- M = max X { s(X) }.')
        self.assertEqual(engine.relation("lo").tuples, {(1,)})
        self.assertEqual(engine.relation("hi").tuples, {("a",)})


if __name__ == "__main__":
    unittest.main()
