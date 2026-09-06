import unittest

from datalog import Engine
from datalog.errors import StratificationError
from datalog.parser import parse
from datalog.safety import compile_rule
from datalog.stratify import build_graph, stratify, strongly_connected_components


def compile_all(text):
    return [compile_rule(rule) for rule in parse(text).rules]


def strata_of(text):
    return stratify(compile_all(text))


class TestDependencyGraph(unittest.TestCase):
    def test_edges_recorded_with_polarity(self):
        graph = build_graph(compile_all("p(X) :- q(X), not r(X)."))
        self.assertEqual(graph.dependencies(("p", 1)), {("q", 1), ("r", 1)})
        self.assertIn((("p", 1), ("r", 1)), graph.negative)
        self.assertNotIn((("p", 1), ("q", 1)), graph.negative)

    def test_aggregate_bodies_count_as_negative_dependencies(self):
        graph = build_graph(compile_all("p(X, N) :- q(X), N = count { r(X, _) }."))
        self.assertIn((("p", 2), ("r", 2)), graph.negative)

    def test_body_predicates_of_undefined_predicates_are_nodes(self):
        graph = build_graph(compile_all("p(X) :- q(X)."))
        self.assertIn(("q", 1), graph.nodes)


class TestSCC(unittest.TestCase):
    def test_self_loop_is_its_own_component(self):
        graph = build_graph(compile_all("p(X) :- e(X, _), p(X)."))
        components = strongly_connected_components(graph)
        self.assertIn([("p", 1)], components)

    def test_mutual_recursion_forms_one_component(self):
        graph = build_graph(compile_all("p(X) :- q(X). q(X) :- p(X)."))
        components = strongly_connected_components(graph)
        recursive = [c for c in components if len(c) > 1]
        self.assertEqual(len(recursive), 1)
        self.assertEqual(set(recursive[0]), {("p", 1), ("q", 1)})

    def test_dependencies_are_emitted_before_dependents(self):
        graph = build_graph(compile_all("c(X) :- b(X). b(X) :- a(X). a(1)."))
        order = [component[0] for component in strongly_connected_components(graph)]
        self.assertLess(order.index(("a", 1)), order.index(("b", 1)))
        self.assertLess(order.index(("b", 1)), order.index(("c", 1)))

    def test_deep_chain_does_not_overflow_the_stack(self):
        # A 4000-link chain would blow a recursive Tarjan implementation.
        depth = 4000
        text = "p0(1).\n" + "".join(
            "p%d(X) :- p%d(X).\n" % (i, i - 1) for i in range(1, depth)
        )
        components = strongly_connected_components(build_graph(compile_all(text)))
        self.assertEqual(len(components), depth)


class TestStratification(unittest.TestCase):
    def test_positive_recursion_stays_in_one_stratum(self):
        strata, stratum_of = strata_of(
            """
            edge(a, b).
            path(X, Y) :- edge(X, Y).
            path(X, Y) :- edge(X, Z), path(Z, Y).
            """
        )
        self.assertEqual(stratum_of[("path", 2)], stratum_of[("edge", 2)])
        self.assertEqual(len(strata), 1)

    def test_negation_raises_the_stratum(self):
        strata, stratum_of = strata_of(
            "n(a). p(a). q(X) :- n(X), not p(X)."
        )
        self.assertGreater(stratum_of[("q", 1)], stratum_of[("p", 1)])
        self.assertEqual(len(strata), 2)

    def test_chained_negation_creates_three_strata(self):
        _, stratum_of = strata_of(
            """
            n(a). p(a).
            q(X) :- n(X), not p(X).
            r(X) :- n(X), not q(X).
            """
        )
        self.assertEqual(stratum_of[("p", 1)], 0)
        self.assertEqual(stratum_of[("q", 1)], 1)
        self.assertEqual(stratum_of[("r", 1)], 2)

    def test_aggregate_raises_the_stratum(self):
        _, stratum_of = strata_of("q(a). p(N) :- N = count { q(_) }.")
        self.assertGreater(stratum_of[("p", 1)], stratum_of[("q", 1)])

    def test_recursion_through_negation_is_rejected(self):
        with self.assertRaises(StratificationError) as caught:
            strata_of("q(a). p(X) :- q(X), not p(X).")
        self.assertIn("negatively", str(caught.exception))

    def test_mutual_recursion_through_negation_is_rejected(self):
        with self.assertRaises(StratificationError):
            strata_of("n(a). p(X) :- n(X), not q(X). q(X) :- n(X), not p(X).")

    def test_recursion_through_an_aggregate_is_rejected(self):
        with self.assertRaises(StratificationError):
            strata_of("q(a, 1). p(X, N) :- q(X, _), N = count { p(X, _) }.")

    def test_empty_program(self):
        strata, stratum_of = stratify([])
        self.assertEqual(strata, [])
        self.assertEqual(stratum_of, {})

    def test_engine_reports_strata(self):
        engine = Engine()
        engine.load("n(a). p(a). q(X) :- n(X), not p(X).")
        engine.run()
        self.assertEqual(len(engine.strata), 2)
        self.assertIn(("q", 1), engine.strata[1])


if __name__ == "__main__":
    unittest.main()
