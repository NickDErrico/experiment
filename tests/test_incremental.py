"""Incremental maintenance: asserting and retracting facts after evaluation.

The unit tests below pin down the interface.  The real work is done by
:class:`TestAgainstRecomputation`, which drives random update sequences through
programs with recursion, negation and aggregates and demands that the
maintained database match one evaluated from scratch, tuple for tuple.  That is
the only check that can catch a bug in DRed's overdeletion or rederivation,
because every such bug is by definition a disagreement with the answer the
engine would have given anyway.
"""

import random
import unittest

from datalog import Delta, Engine
from datalog.errors import DatalogError


def relations(engine):
    """Every non-empty relation as ``{signature: frozenset(tuples)}``."""
    return {
        signature: frozenset(relation.tuples)
        for signature, relation in engine.relations.items()
        if relation.tuples
    }


class TestAssertAndRetract(unittest.TestCase):
    GRAPH = """
        path(X, Y) :- edge(X, Y).
        path(X, Y) :- edge(X, Z), path(Z, Y).
    """

    def engine(self, facts="edge(a, b). edge(b, c)."):
        engine = Engine()
        engine.load(self.GRAPH)
        engine.load(facts)
        engine.run()
        return engine

    def test_asserting_a_fact_derives_its_consequences(self):
        engine = self.engine()
        delta = engine.assert_fact("edge(c, d)")
        self.assertEqual(
            sorted(engine.relation("path").tuples),
            [("a", "b"), ("a", "c"), ("a", "d"), ("b", "c"), ("b", "d"), ("c", "d")],
        )
        self.assertEqual(
            [str(atom) for atom in delta.added_facts("path")],
            ["path(a, d)", "path(b, d)", "path(c, d)"],
        )
        self.assertEqual(delta.removed, {})

    def test_retracting_a_fact_removes_what_rested_on_it(self):
        engine = self.engine("edge(a, b). edge(b, c). edge(c, d).")
        delta = engine.retract_fact("edge(b, c)")
        self.assertEqual(
            sorted(engine.relation("path").tuples), [("a", "b"), ("c", "d")]
        )
        self.assertEqual(
            [str(atom) for atom in delta.removed_facts("path")],
            ["path(a, c)", "path(a, d)", "path(b, c)", "path(b, d)"],
        )

    def test_a_fact_with_another_derivation_survives_retraction(self):
        """The point of the rederive half of DRed."""
        engine = Engine()
        engine.load(self.GRAPH)
        # a -> b directly, and also a -> z -> b.
        engine.load("edge(a, b). edge(a, z). edge(z, b).")
        engine.run()
        delta = engine.retract_fact("edge(a, b)")
        self.assertIn(("a", "b"), engine.relation("path").tuples)
        self.assertEqual([str(a) for a in delta.removed_facts("path")], [])
        self.assertEqual([str(a) for a in delta.removed_facts("edge")], ["edge(a, b)"])

    def test_retracting_a_cycle_edge_removes_the_whole_cycle(self):
        engine = self.engine("edge(a, b). edge(b, c). edge(c, a).")
        self.assertIn(("a", "a"), engine.relation("path").tuples)
        engine.retract_fact("edge(c, a)")
        self.assertEqual(
            sorted(engine.relation("path").tuples),
            [("a", "b"), ("a", "c"), ("b", "c")],
        )

    def test_batch_update_applies_removals_before_additions(self):
        engine = self.engine()
        delta = engine.update(add=["edge(c, d)"], remove=["edge(a, b)"])
        self.assertEqual(sorted(engine.relation("edge").tuples), [("b", "c"), ("c", "d")])
        self.assertIn(("b", "d"), delta.added.get(("path", 2), set()))
        self.assertIn(("a", "c"), delta.removed.get(("path", 2), set()))

    def test_asserting_and_retracting_the_same_fact_leaves_it_asserted(self):
        engine = self.engine()
        delta = engine.update(add=["edge(a, b)"], remove=["edge(a, b)"])
        self.assertFalse(delta)
        self.assertTrue(engine.is_asserted("edge(a, b)"))

    def test_retracting_a_derived_fact_changes_nothing(self):
        engine = self.engine()
        self.assertFalse(engine.retract_fact("path(a, c)"))
        self.assertIn(("a", "c"), engine.relation("path").tuples)

    def test_retracting_an_unknown_fact_changes_nothing(self):
        engine = self.engine()
        self.assertFalse(engine.retract_fact("edge(q, q)"))

    def test_asserting_a_known_fact_changes_nothing_and_adds_no_rule(self):
        engine = self.engine()
        before = len(engine.rules)
        self.assertFalse(engine.assert_fact("edge(a, b)"))
        self.assertEqual(len(engine.rules), before)

    def test_empty_update_is_a_no_op(self):
        engine = self.engine()
        self.assertFalse(engine.update())

    def test_update_accepts_a_bare_fact(self):
        engine = self.engine()
        self.assertTrue(engine.update(add="edge(c, d)"))

    def test_update_runs_the_program_first_if_it_has_not_run(self):
        engine = Engine()
        engine.load(self.GRAPH)
        engine.load("edge(a, b).")
        delta = engine.update(add=["edge(b, c)"])  # never called run()
        self.assertIn(("a", "c"), engine.relation("path").tuples)
        self.assertIn(("a", "c"), delta.added[("path", 2)])

    def test_update_rejects_a_non_ground_fact(self):
        engine = self.engine()
        with self.assertRaises(DatalogError):
            engine.assert_fact("edge(a, X)")

    def test_update_rejects_an_arity_conflict(self):
        engine = self.engine()
        with self.assertRaises(DatalogError):
            engine.assert_fact("edge(a, b, c)")

    def test_is_asserted_distinguishes_facts_from_conclusions(self):
        engine = self.engine()
        self.assertTrue(engine.is_asserted("edge(a, b)"))
        self.assertFalse(engine.is_asserted("path(a, c)"))
        self.assertFalse(engine.is_asserted("edge(q, q)"))

    def test_queries_and_relations_see_the_update(self):
        engine = self.engine()
        engine.assert_fact("edge(c, d)")
        self.assertEqual([row["X"] for row in engine.query("path(a, X)")], ["b", "c", "d"])
        engine.retract_fact("edge(a, b)")
        self.assertEqual([row["X"] for row in engine.query("path(a, X)")], [])


class TestNegationAndAggregates(unittest.TestCase):
    """The cases where a change below a stratum moves things in both directions."""

    def test_retracting_below_a_negation_adds_facts_above(self):
        engine = Engine()
        engine.load("blocked(b). ok(X) :- item(X), not blocked(X). item(a). item(b).")
        engine.run()
        self.assertEqual(sorted(engine.relation("ok").tuples), [("a",)])
        delta = engine.retract_fact("blocked(b)")
        self.assertEqual(sorted(engine.relation("ok").tuples), [("a",), ("b",)])
        self.assertEqual([str(a) for a in delta.added_facts("ok")], ["ok(b)"])

    def test_asserting_below_a_negation_removes_facts_above(self):
        engine = Engine()
        engine.load("ok(X) :- item(X), not blocked(X). item(a). item(b).")
        engine.run()
        delta = engine.assert_fact("blocked(b)")
        self.assertEqual(sorted(engine.relation("ok").tuples), [("a",)])
        self.assertEqual([str(a) for a in delta.removed_facts("ok")], ["ok(b)"])

    def test_a_negation_still_blocked_by_a_surviving_fact_stays_blocked(self):
        """Two reasons to be blocked; taking one away must not unblock."""
        engine = Engine()
        engine.load(
            "ok(X) :- item(X), not blocked(X, _). item(a)."
            "blocked(a, one). blocked(a, two)."
        )
        engine.run()
        self.assertEqual(sorted(engine.relation("ok").tuples), [])
        engine.retract_fact("blocked(a, one)")
        self.assertEqual(sorted(engine.relation("ok").tuples), [])
        engine.retract_fact("blocked(a, two)")
        self.assertEqual(sorted(engine.relation("ok").tuples), [("a",)])

    def test_aggregates_are_recomputed_when_their_input_moves(self):
        engine = Engine()
        engine.load("total(P, N) :- person(P), N = count { owns(P, _) }. person(alice).")
        engine.load("owns(alice, car). owns(alice, bike).")
        engine.run()
        self.assertEqual(sorted(engine.relation("total").tuples), [("alice", 2)])
        delta = engine.assert_fact("owns(alice, boat)")
        self.assertEqual(sorted(engine.relation("total").tuples), [("alice", 3)])
        self.assertEqual([str(a) for a in delta.added_facts("total")], ["total(alice, 3)"])
        self.assertEqual(
            [str(a) for a in delta.removed_facts("total")], ["total(alice, 2)"]
        )
        engine.update(remove=["owns(alice, car)", "owns(alice, bike)"])
        self.assertEqual(sorted(engine.relation("total").tuples), [("alice", 1)])

    def test_an_aggregate_whose_value_does_not_move_is_left_alone(self):
        engine = Engine()
        engine.load("n(P, C) :- p(P), C = count { q(P, _) }. p(a). p(b).")
        engine.load("q(a, one). q(b, one).")
        engine.run()
        delta = engine.assert_fact("q(b, two)")
        self.assertEqual(delta.added[("n", 2)], {("b", 2)})
        self.assertEqual(delta.removed[("n", 2)], {("b", 1)})
        self.assertIn(("a", 1), engine.relation("n").tuples)

    def test_change_propagates_through_several_strata(self):
        engine = Engine()
        engine.load(
            """
            reach(X, Y) :- link(X, Y).
            reach(X, Y) :- link(X, Z), reach(Z, Y).
            isolated(X) :- place(X), not reach(X, _).
            fanout(X, N) :- place(X), N = count { reach(X, _) }.
            hub(X) :- fanout(X, N), N >= 2, not isolated(X).
            place(a). place(b). place(c). place(d).
            link(a, b). link(b, c).
            """
        )
        engine.run()
        self.assertEqual(sorted(engine.relation("hub").tuples), [("a",)])
        self.assertEqual(sorted(engine.relation("isolated").tuples), [("c",), ("d",)])
        engine.assert_fact("link(c, d)")
        self.assertEqual(sorted(engine.relation("hub").tuples), [("a",), ("b",)])
        self.assertEqual(sorted(engine.relation("isolated").tuples), [("d",)])
        engine.retract_fact("link(a, b)")
        self.assertEqual(sorted(engine.relation("hub").tuples), [("b",)])
        self.assertEqual(sorted(engine.relation("isolated").tuples), [("a",), ("d",)])


class TestDelta(unittest.TestCase):
    def delta(self):
        engine = Engine()
        engine.load("p(X) :- q(X). q(a).")
        engine.run()
        return engine.assert_fact("q(b)")

    def test_truthiness_and_size(self):
        delta = self.delta()
        self.assertTrue(delta)
        self.assertEqual(len(delta), 2)
        self.assertFalse(Delta())
        self.assertEqual(len(Delta()), 0)

    def test_format_is_a_diff(self):
        self.assertEqual(str(self.delta()), "+ p(b)\n+ q(b)")

    def test_format_can_be_narrowed_to_one_predicate(self):
        self.assertEqual(self.delta().format("p"), "+ p(b)")

    def test_predicates_lists_what_moved(self):
        self.assertEqual(self.delta().predicates, [("p", 1), ("q", 1)])

    def test_to_dict_is_json_shaped(self):
        payload = self.delta().to_dict()
        self.assertEqual(payload["added"], ["p(b)", "q(b)"])
        self.assertEqual(payload["removed"], [])
        self.assertEqual(payload["stats"]["mode"], "incremental")

    def test_repr(self):
        self.assertEqual(repr(self.delta()), "<Delta +2 -0>")

    def test_removals_are_reported_with_a_minus(self):
        engine = Engine()
        engine.load("p(X) :- q(X). q(a).")
        engine.run()
        self.assertEqual(str(engine.retract_fact("q(a)")), "- p(a)\n- q(a)")


class TestFallbackToRecomputation(unittest.TestCase):
    def test_a_fact_for_an_unknown_predicate_recomputes(self):
        engine = Engine()
        engine.load("p(X) :- q(X). q(a).")
        engine.run()
        delta = engine.assert_fact("brand(new)")
        self.assertEqual(delta.stats["mode"], "recompute")
        self.assertEqual([str(a) for a in delta.added_facts()], ["brand(new)"])
        self.assertIn(("new",), engine.relation("brand").tuples)

    def test_recomputation_reports_the_same_change_as_maintenance(self):
        source = """
            path(X, Y) :- edge(X, Y).
            path(X, Y) :- edge(X, Z), path(Z, Y).
            edge(a, b). edge(b, c).
        """
        maintained = Engine()
        maintained.load(source)
        maintained.run()
        delta = maintained.assert_fact("edge(c, d)")

        recomputed = Engine()
        recomputed.load(source)
        recomputed.load("edge(c, d).")
        recomputed.run()
        self.assertEqual(relations(maintained), relations(recomputed))
        self.assertEqual(
            [str(a) for a in delta.added_facts("path")],
            ["path(a, d)", "path(b, d)", "path(c, d)"],
        )


class TestExplainAfterUpdates(unittest.TestCase):
    """Proofs must stay well founded once tuples have come and gone."""

    def test_a_rederived_fact_can_still_be_explained(self):
        engine = Engine(track_derivations=True)
        engine.load(
            """
            path(X, Y) :- edge(X, Y).
            path(X, Y) :- edge(X, Z), path(Z, Y).
            edge(a, b). edge(a, z). edge(z, b).
            """
        )
        engine.run()
        engine.retract_fact("edge(a, b)")
        derivation = engine.explain("path(a, b)")
        self.assertIsNotNone(derivation)
        self.assertEqual(
            [str(a) for a in derivation.support()], ["edge(a, z)", "edge(z, b)"]
        )

    def test_proofs_stay_acyclic_through_a_sequence_of_updates(self):
        rng = random.Random(20260907)
        engine = Engine(track_derivations=True)
        engine.load(
            """
            path(X, Y) :- edge(X, Y).
            path(X, Y) :- edge(X, Z), path(Z, Y).
            loop(X) :- node(X), path(X, X).
            node(a). node(b). node(c). node(d).
            """
        )
        engine.load("edge(a, b). edge(b, c). edge(c, a).")
        engine.run()

        names = ["a", "b", "c", "d"]
        for _ in range(25):
            edge = (rng.choice(names), rng.choice(names))
            text = "edge(%s, %s)" % edge
            if engine.is_asserted(text):
                engine.retract_fact(text)
            else:
                engine.assert_fact(text)
            for signature, relation in engine.relations.items():
                for tup in relation.tuples:
                    fact = "%s(%s)" % (signature[0], ", ".join(tup))
                    with self.subTest(fact=fact):
                        self._check_proof(engine, fact)

    def _check_proof(self, engine, fact):
        derivation = engine.explain(fact)
        self.assertIsNotNone(derivation, "%s was derived but cannot be explained" % fact)
        self._descend(derivation, frozenset())
        for leaf in derivation.support():
            tup = tuple(term.value for term in leaf.terms)
            self.assertIn(tup, engine._relation(leaf.signature).tuples)

    def _descend(self, node, ancestors):
        key = str(node.atom)
        self.assertNotIn(key, ancestors, "%s appears beneath itself" % key)
        for premise in node.premises:
            if hasattr(premise, "premises"):
                self._descend(premise, ancestors | {key})


class TestAgainstRecomputation(unittest.TestCase):
    """The differential test that actually guards DRed.

    A maintained database and a freshly evaluated one must be identical after
    every update, and the reported delta must be exactly the difference between
    the database before the update and after it.  Overdeleting too much shows up
    as a missing tuple, overdeleting too little as a phantom one, and getting
    the delta wrong shows up on its own.
    """

    PROGRAMS = {
        "recursion": """
            path(X, Y) :- edge(X, Y).
            path(X, Y) :- edge(X, Z), path(Z, Y).
        """,
        "mutual recursion": """
            path(X, Y) :- edge(X, Y).
            path(X, Y) :- step(X, Z), path(Z, Y).
            step(X, Y) :- edge(X, Y).
            step(X, Y) :- edge(Y, X).
        """,
        "negation": """
            path(X, Y) :- edge(X, Y).
            path(X, Y) :- edge(X, Z), path(Z, Y).
            unreached(X, Y) :- node(X), node(Y), not path(X, Y).
            sink(X) :- node(X), not edge(X, _).
            direct(X, Y) :- path(X, Y), not indirect(X, Y).
            indirect(X, Y) :- edge(X, Z), path(Z, Y).
        """,
        "aggregates": """
            path(X, Y) :- edge(X, Y).
            path(X, Y) :- edge(X, Z), path(Z, Y).
            outdeg(X, N) :- node(X), N = count { edge(X, _) }.
            reach(X, N) :- node(X), N = count { path(X, _) }.
            busy(X) :- outdeg(X, N), N >= 2.
            widest(M) :- M = max N { outdeg(_, N) }.
            edges(N) :- N = count { edge(_, _) }.
        """,
        "layered": """
            a(X, Y) :- edge(X, Y).
            a(X, Y) :- edge(X, Z), a(Z, Y).
            b(X) :- node(X), not a(X, X).
            c(X, Y) :- a(X, Y), b(X), b(Y).
            d(X, N) :- b(X), N = count { c(X, _) }.
            e(X) :- d(X, N), N > 0, not f(X).
            f(X) :- node(X), not c(X, _).
            g(N) :- N = sum M { d(_, M) }.
        """,
        "arithmetic": """
            path(X, Y) :- edge(X, Y).
            path(X, Y) :- edge(X, Z), path(Z, Y).
            span(X, Y, S) :- path(X, Y), S = X + Y.
            far(X, Y) :- span(X, Y, S), S > 5.
        """,
    }

    def _fresh(self, program, nodes, edges):
        engine = Engine()
        engine.load(program)
        engine.load(
            "".join("node(%d)." % n for n in sorted(nodes))
            + "".join("edge(%d, %d)." % e for e in sorted(edges))
        )
        engine.run()
        return engine

    def _run_one(self, name, program, seed):
        rng = random.Random(seed)
        nodes = list(range(rng.randint(2, 5)))
        every = [(a, b) for a in nodes for b in nodes]
        edges = set(rng.sample(every, rng.randint(0, min(6, len(every)))))
        present = set(nodes)

        engine = self._fresh(program, present, edges)
        for step in range(8):
            before = relations(engine)
            adds, removes, touched = [], [], set()
            for _ in range(rng.randint(1, 3)):
                if rng.random() < 0.25:
                    node = rng.choice(nodes)
                    if ("node", node) in touched:
                        continue
                    touched.add(("node", node))
                    if node in present:
                        present.discard(node)
                        removes.append("node(%d)" % node)
                    else:
                        present.add(node)
                        adds.append("node(%d)" % node)
                    continue
                edge = rng.choice(every)
                if edge in touched:
                    continue
                touched.add(edge)
                if edge in edges:
                    edges.discard(edge)
                    removes.append("edge(%d, %d)" % edge)
                else:
                    edges.add(edge)
                    adds.append("edge(%d, %d)" % edge)
            if not adds and not removes:
                continue

            delta = engine.update(add=adds, remove=removes)
            context = "%s seed=%d step=%d add=%s remove=%s" % (
                name,
                seed,
                step,
                adds,
                removes,
            )
            after = relations(engine)
            self.assertEqual(
                after, relations(self._fresh(program, present, edges)), context
            )
            for signature in set(before) | set(after):
                was = before.get(signature, frozenset())
                now = after.get(signature, frozenset())
                self.assertEqual(
                    delta.added.get(signature, set()), set(now - was), context
                )
                self.assertEqual(
                    delta.removed.get(signature, set()), set(was - now), context
                )

    def test_maintenance_matches_recomputation(self):
        for name, program in self.PROGRAMS.items():
            with self.subTest(program=name):
                for seed in range(25):
                    self._run_one(name, program, seed)


if __name__ == "__main__":
    unittest.main()
