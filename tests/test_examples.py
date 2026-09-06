"""The bundled examples must stay correct: they are the documentation."""

import io
import os
import unittest
from contextlib import redirect_stderr, redirect_stdout

from datalog import Engine, cli

EXAMPLES = os.path.join(os.path.dirname(os.path.dirname(os.path.abspath(__file__))), "examples")


def load(name):
    engine = Engine()
    with open(os.path.join(EXAMPLES, name), "r", encoding="utf-8") as handle:
        engine.load(handle.read(), name)
    engine.run()
    return engine


class TestExamplesRun(unittest.TestCase):
    def test_every_example_runs_cleanly(self):
        names = sorted(n for n in os.listdir(EXAMPLES) if n.endswith(".dl"))
        self.assertTrue(names, "no examples found")
        for name in names:
            with self.subTest(example=name):
                out, err = io.StringIO(), io.StringIO()
                with redirect_stdout(out), redirect_stderr(err):
                    code = cli.main(
                        ["run", os.path.join(EXAMPLES, name), "--warn-undefined"]
                    )
                self.assertEqual(code, 0)
                self.assertNotIn("warning:", err)
                self.assertNotIn("no answers.", out)


class TestAncestors(unittest.TestCase):
    def setUp(self):
        self.engine = load("ancestors.dl")

    def test_ancestors(self):
        self.assertEqual(
            self.engine.query("ancestor(alice, X)").rows,
            [("betty",), ("bob",), ("carol",), ("chris",), ("dave",)],
        )

    def test_siblings_exclude_self(self):
        self.assertEqual(self.engine.query("sibling(bob, X)").rows, [("betty",)])
        self.assertFalse(self.engine.query("sibling(bob, bob)"))

    def test_root_and_descendant_count(self):
        self.assertEqual(self.engine.relation("root").tuples, {("alice",)})
        self.assertEqual(self.engine.relation("descendants").tuples, {("alice", 5)})


class TestAccessControl(unittest.TestCase):
    def setUp(self):
        self.engine = load("access.dl")

    def test_role_inheritance_is_transitive(self):
        self.assertEqual(
            self.engine.query("hasRole(alice, R)").rows,
            [("admin",), ("employee",), ("engineer",)],
        )

    def test_denial_overrides_a_grant(self):
        # Both users genuinely hold the permission through a role, and the
        # explicit denial takes it away again.
        self.assertTrue(self.engine.query("granted(carol, read, docs)"))
        self.assertFalse(self.engine.query("allowed(carol, read, docs)"))
        self.assertTrue(self.engine.query("granted(bob, write, repo)"))
        self.assertFalse(self.engine.query("allowed(bob, write, repo)"))

    def test_admin_can_deploy(self):
        self.assertTrue(self.engine.query("allowed(alice, deploy, prod)"))

    def test_permission_counts(self):
        self.assertEqual(
            self.engine.relation("permissionCount").tuples,
            {("alice", 4), ("bob", 2), ("carol", 0), ("dan", 0)},
        )

    def test_user_with_no_role_is_powerless(self):
        self.assertEqual(self.engine.relation("powerless").tuples, {("dan",)})


class TestPointsTo(unittest.TestCase):
    def setUp(self):
        self.engine = load("pointsto.dl")

    def test_load_through_a_pointer(self):
        # c = *p, p -> a, a -> x, therefore c -> x
        self.assertEqual(self.engine.query("pointsTo(c, W)").rows, [("x",)])

    def test_store_through_a_pointer(self):
        # *d = e, d -> q, e -> y, therefore q -> y
        self.assertEqual(self.engine.query("pointsTo(q, W)").rows, [("y",)])

    def test_assignment_is_transitive(self):
        self.assertEqual(self.engine.query("pointsTo(f, W)").rows, [("x",)])

    def test_alias_is_symmetric_and_irreflexive(self):
        aliases = self.engine.relation("mayAlias").tuples
        self.assertTrue(all(x != y for x, y in aliases))
        self.assertTrue(all((y, x) in aliases for x, y in aliases))


class TestGraph(unittest.TestCase):
    def setUp(self):
        self.engine = load("graph.dl")

    def test_sources_and_sinks(self):
        self.assertEqual(self.engine.relation("source").tuples, {("a",), ("f",)})
        self.assertEqual(self.engine.relation("sink").tuples, {("g",)})

    def test_cycle_detection(self):
        self.assertEqual(
            self.engine.relation("onCycle").tuples,
            {("b",), ("c",), ("d",), ("e",)},
        )

    def test_shortest_path_cost(self):
        # a -> c (2) -> b (1) -> d (5) -> e (3) = 11, cheaper than a -> b -> d -> e.
        self.assertEqual(self.engine.query("shortest(a, e, C)").rows, [(11,)])

    def test_degrees(self):
        self.assertEqual(self.engine.query("outDegree(a, N)").rows, [(2,)])
        self.assertEqual(self.engine.query("inDegree(g, N)").rows, [(1,)])
        self.assertEqual(self.engine.query("outDegree(g, N)").rows, [(0,)])


if __name__ == "__main__":
    unittest.main()
