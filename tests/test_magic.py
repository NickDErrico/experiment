"""Tests for the magic-set (demand) transformation.

The transformation must not change what a query answers -- only how much work
answering it takes.  That makes it a natural fit for differential testing, and
the bulk of this file is exactly that: random programs, random queries, and an
assertion that demand-driven evaluation and whole-program evaluation agree row
for row.  Everything else here checks the two things a differential test cannot
see: that the transformation actually *fires* (rather than quietly falling back
every time and trivially agreeing with itself), and that when it fires it
really does less work.
"""

import random
import unittest

from datalog import Engine
from datalog.engine import _coerce_query, _query_variables
from datalog.magic import GOAL, magic_name, transform


def transform_query(engine, text):
    """Transform ``text`` against ``engine``'s rules, as ``query()`` would."""
    query = _coerce_query(text)
    return transform(engine.rules, query, _query_variables(query.body))


def demand_stats(engine, text):
    """Run one demand query and return its statistics, or ``None``."""
    return engine.query(text, demand=True).stats


class MagicAnswersTest(unittest.TestCase):
    """Demand-driven answers must equal whole-program answers."""

    def assertSameAnswers(self, engine, goal, msg=None):
        full = engine.query(goal)
        demand = engine.query(goal, demand=True)
        self.assertEqual(demand.variables, full.variables, msg)
        self.assertEqual(demand.rows, full.rows, msg)
        return demand

    def test_reachability(self):
        engine = Engine()
        engine.load(
            """
            edge(a, b).  edge(b, c).  edge(c, d).  edge(x, y).
            path(X, Y) :- edge(X, Y).
            path(X, Y) :- edge(X, Z), path(Z, Y).
            """
        )
        result = self.assertSameAnswers(engine, "path(a, W)")
        self.assertEqual([row["W"] for row in result], ["b", "c", "d"])
        self.assertIsNotNone(result.stats, "expected the transformation to fire")

    def test_ground_query_says_yes_or_no(self):
        engine = Engine()
        engine.load(
            """
            edge(a, b).  edge(b, c).  edge(p, q).
            path(X, Y) :- edge(X, Y).
            path(X, Y) :- edge(X, Z), path(Z, Y).
            """
        )
        self.assertTrue(self.assertSameAnswers(engine, "path(a, c)"))
        self.assertFalse(self.assertSameAnswers(engine, "path(a, q)"))

    def test_binding_the_second_argument(self):
        engine = Engine()
        engine.load(
            """
            edge(a, b).  edge(b, c).  edge(c, d).
            path(X, Y) :- edge(X, Y).
            path(X, Y) :- path(X, Z), edge(Z, Y).
            """
        )
        result = self.assertSameAnswers(engine, "path(Who, d)")
        self.assertEqual([row["Who"] for row in result], ["a", "b", "c"])

    def test_conjunctive_query_with_a_filter(self):
        engine = Engine()
        engine.load(
            """
            edge(a, b).  edge(b, c).  edge(c, d).
            path(X, Y) :- edge(X, Y).
            path(X, Y) :- edge(X, Z), path(Z, Y).
            rank(b, 1).  rank(c, 2).  rank(d, 3).
            """
        )
        self.assertSameAnswers(engine, "path(a, W), rank(W, R), R >= 2")

    def test_repeated_variable_in_the_goal(self):
        engine = Engine()
        engine.load(
            """
            edge(a, b).  edge(b, a).  edge(c, d).
            path(X, Y) :- edge(X, Y).
            path(X, Y) :- edge(X, Z), path(Z, Y).
            """
        )
        self.assertSameAnswers(engine, "path(N, N)")
        self.assertSameAnswers(engine, "path(a, Y), path(Y, a)")

    def test_anonymous_variable_is_never_treated_as_bound(self):
        engine = Engine()
        engine.load(
            """
            edge(a, b).  edge(b, c).  edge(q, r).
            path(X, Y) :- edge(X, Y).
            path(X, Y) :- edge(X, Z), path(Z, Y).
            leaves(X) :- path(X, _).
            """
        )
        self.assertSameAnswers(engine, "leaves(Who)")
        self.assertSameAnswers(engine, "path(a, _)")

    def test_negation(self):
        engine = Engine()
        engine.load(
            """
            parent(alice, bob).  parent(bob, carol).  parent(dan, erin).
            ancestor(X, Y) :- parent(X, Y).
            ancestor(X, Y) :- parent(X, Z), ancestor(Z, Y).
            unrelated(X, Y) :- person(X), person(Y), X != Y, not ancestor(X, Y).
            person(P) :- parent(P, _).
            person(P) :- parent(_, P).
            """
        )
        self.assertSameAnswers(engine, "unrelated(alice, Who)")
        self.assertSameAnswers(engine, "ancestor(alice, Who)")

    def test_mutual_recursion(self):
        engine = Engine()
        engine.load(
            """
            step(a, b).  step(b, c).  step(c, d).  step(d, e).
            even(X, X) :- node(X).
            even(X, Z) :- odd(X, Y), step(Y, Z).
            odd(X, Z) :- even(X, Y), step(Y, Z).
            node(X) :- step(X, _).
            node(Y) :- step(_, Y).
            """
        )
        self.assertSameAnswers(engine, "even(a, W)")
        self.assertSameAnswers(engine, "odd(a, W)")

    def test_arithmetic_in_a_demanded_rule(self):
        engine = Engine()
        engine.load(
            """
            edge(a, b, 3).  edge(b, c, 4).  edge(a, c, 9).
            cost(X, Y, C) :- edge(X, Y, C).
            cost(X, Y, C) :- edge(X, Z, C1), cost(Z, Y, C2), C = C1 + C2.
            """
        )
        self.assertSameAnswers(engine, "cost(a, c, C)")

    def test_facts_of_a_derived_predicate_are_demanded_too(self):
        engine = Engine()
        engine.load(
            """
            path(seed, one).
            edge(one, two).  edge(other, thing).
            path(X, Y) :- edge(X, Y).
            path(X, Y) :- path(X, Z), edge(Z, Y).
            """
        )
        result = self.assertSameAnswers(engine, "path(seed, W)")
        self.assertEqual([row["W"] for row in result], ["one", "two"])

    def test_engine_relations_are_left_untouched(self):
        engine = Engine()
        engine.load(
            """
            edge(a, b).  edge(b, c).  edge(x, y).
            path(X, Y) :- edge(X, Y).
            path(X, Y) :- edge(X, Z), path(Z, Y).
            """
        )
        engine.query("path(a, W)", demand=True)
        # The demand run happens in a scratch engine, so asking this one for a
        # relation still gets the whole thing.
        self.assertEqual(
            engine.relation("path").tuples,
            {("a", "b"), ("b", "c"), ("a", "c"), ("x", "y")},
        )


class MagicFallbackTest(unittest.TestCase):
    """When the transformation declines, the query is still answered."""

    def test_declines_when_nothing_is_bound(self):
        engine = Engine()
        engine.load(
            """
            edge(a, b).  edge(b, c).
            path(X, Y) :- edge(X, Y).
            path(X, Y) :- edge(X, Z), path(Z, Y).
            """
        )
        # Every argument is free, so every guard would admit everything: the
        # rewrite would be the original program plus a join per rule.
        self.assertIsNone(transform_query(engine, "path(X, Y)"))
        self.assertIsNone(demand_stats(engine, "path(X, Y)"))
        self.assertEqual(
            engine.query("path(X, Y)", demand=True).rows,
            engine.query("path(X, Y)").rows,
        )

    def test_declines_on_aggregates(self):
        engine = Engine()
        engine.load(
            """
            edge(a, b).  edge(a, c).  edge(b, c).
            path(X, Y) :- edge(X, Y).
            path(X, Y) :- edge(X, Z), path(Z, Y).
            reach(X, N) :- edge(X, _), N = count { path(X, _) }.
            """
        )
        self.assertIsNone(transform_query(engine, "reach(a, N)"))
        self.assertEqual(
            engine.query("reach(a, N)", demand=True).rows,
            engine.query("reach(a, N)").rows,
        )
        # ... but a query that does not reach the aggregate is still rewritten.
        self.assertIsNotNone(transform_query(engine, "path(a, W)"))

    def test_declines_when_the_rewrite_cannot_be_stratified(self):
        # `blocked` is read under negation by a rule in `path`'s own recursion,
        # and demand for it flows back through `path`.  The original program
        # stratifies; the rewrite cannot.
        engine = Engine()
        engine.load(
            """
            edge(a, b).  edge(b, c).  edge(c, d).
            blocked(X, Y) :- edge(X, Y), toll(X).
            toll(b).
            path(X, Y) :- edge(X, Y), not blocked(X, Y).
            path(X, Y) :- path(X, Z), edge(Z, Y), not blocked(Z, Y).
            """
        )
        expected = engine.query("path(a, W)")
        result = engine.query("path(a, W)", demand=True)
        self.assertEqual(result.rows, expected.rows)

    def test_declines_rather_than_specialising_without_bound(self):
        # `path` is reached under two binding patterns here, so a budget of one
        # adornment per predicate is not enough and the rewrite is abandoned.
        engine = Engine()
        engine.load(
            """
            edge(a, b).  edge(b, c).
            path(X, Y) :- edge(X, Y).
            path(X, Y) :- edge(X, Z), path(Z, Y).
            round(X, Y) :- path(X, Y), path(Y, X).
            """
        )
        query = _coerce_query("round(a, W)")
        variables = _query_variables(query.body)
        self.assertIsNotNone(transform(engine.rules, query, variables))
        self.assertIsNone(
            transform(engine.rules, query, variables, max_adornments=1)
        )
        self.assertIsNone(transform(engine.rules, query, variables, max_rules=1))

    def test_undefined_predicate_is_empty_either_way(self):
        engine = Engine()
        engine.load("p(X) :- q(X), typo(X).  q(a).  q(b).")
        self.assertEqual(engine.query("p(a)", demand=True).rows, [])
        self.assertEqual(engine.query("p(a)").rows, [])


class MagicWorkTest(unittest.TestCase):
    """The point of the exercise: derive less."""

    def _islands(self, count, size):
        """`count` disjoint paths of `size` nodes; only the first is asked about."""
        lines = []
        for island in range(count):
            for step in range(size - 1):
                lines.append(
                    "edge(n%d_%d, n%d_%d)." % (island, step, island, step + 1)
                )
        lines.append("path(X, Y) :- edge(X, Y).")
        lines.append("path(X, Y) :- edge(X, Z), path(Z, Y).")
        return "\n".join(lines)

    def test_demand_derives_far_fewer_tuples(self):
        engine = Engine()
        engine.load(self._islands(count=12, size=12))
        goal = "path(n0_0, W)"

        self.assertEqual(
            engine.query(goal, demand=True).rows, engine.query(goal).rows
        )

        whole_program = engine.stats["tuples"]
        demanded = engine.query(goal, demand=True).stats["tuples"]
        # One island's worth of work instead of twelve.  The bound is loose on
        # purpose -- the claim is the order of magnitude, not a tuple count.
        self.assertLess(demanded, whole_program / 4)

    def test_demand_does_not_explore_the_whole_graph(self):
        engine = Engine()
        engine.load(self._islands(count=6, size=8))
        engine.run()
        # A ground query that fails still only looks at the island it started
        # in, rather than closing the entire relation first.
        result = engine.query("path(n0_0, n5_7)", demand=True)
        self.assertFalse(result)
        self.assertLess(result.stats["tuples"], engine.stats["tuples"] / 4)


class MagicStructureTest(unittest.TestCase):
    """The shape of the rewritten program."""

    PROGRAM = """
        edge(a, b).  edge(b, c).
        path(X, Y) :- edge(X, Y).
        path(X, Y) :- edge(X, Z), path(Z, Y).
    """

    def rewritten(self, goal):
        engine = Engine()
        engine.load(self.PROGRAM)
        return [str(rule) for rule in transform_query(engine, goal)]

    def test_seeds_the_query_and_propagates_demand(self):
        rules = self.rewritten("path(a, W)")
        magic = magic_name(("path", 2), "bf")
        self.assertIn("%s(a) :- %s." % (magic, magic_name((GOAL, 1), "f")), rules)
        self.assertIn("%s(Z) :- %s(X), edge(X, Z)." % (magic, magic), rules)
        for rule in rules:
            if rule.startswith("path("):
                self.assertIn(magic, rule, "every path rule must be guarded")

    def test_extensional_facts_are_carried_over_unguarded(self):
        rules = self.rewritten("path(a, W)")
        self.assertIn("edge(a, b).", rules)
        self.assertIn("edge(b, c).", rules)

    def test_invented_names_cannot_collide_with_user_predicates(self):
        # The lexer cannot produce an identifier containing '#', so no program
        # can name a predicate that clashes with a magic one.
        self.assertIn("#", GOAL)
        self.assertIn("#", magic_name(("p", 1), "b"))
        engine = Engine()
        engine.load(self.PROGRAM)
        for name, _ in engine.predicates():
            self.assertNotIn("#", name)


class MagicRandomTest(unittest.TestCase):
    """Random programs, random queries, same answers."""

    PROGRAMS = [
        """
        path(X, Y) :- edge(X, Y).
        path(X, Y) :- edge(X, Z), path(Z, Y).
        """,
        """
        path(X, Y) :- edge(X, Y).
        path(X, Y) :- path(X, Z), edge(Z, Y).
        """,
        """
        path(X, Y) :- edge(X, Y).
        path(X, Y) :- path(X, Z), path(Z, Y).
        """,
        """
        node(X) :- edge(X, _).
        node(Y) :- edge(_, Y).
        path(X, Y) :- edge(X, Y).
        path(X, Y) :- edge(X, Z), path(Z, Y).
        cyclic(X) :- path(X, X).
        acyclic(X) :- node(X), not cyclic(X).
        stranded(X, Y) :- node(X), node(Y), not path(X, Y).
        """,
        """
        node(X) :- edge(X, _).
        node(Y) :- edge(_, Y).
        even(X, X) :- node(X).
        even(X, Z) :- odd(X, Y), edge(Y, Z).
        odd(X, Z) :- even(X, Y), edge(Y, Z).
        both(X, Y) :- even(X, Y), odd(X, Y).
        """,
        """
        reach(X, Y) :- edge(X, Y).
        reach(X, Y) :- edge(X, Z), reach(Z, Y).
        hop(X, Y, 1) :- edge(X, Y).
        hop(X, Y, N) :- edge(X, Z), hop(Z, Y, M), N = M + 1, N < 5.
        far(X, Y) :- hop(X, Y, N), N > 2.
        """,
    ]

    GOALS = [
        "path(%s, W)",
        "path(W, %s)",
        "path(%s, %s)",
        "node(%s)",
        "cyclic(%s)",
        "acyclic(%s)",
        "stranded(%s, W)",
        "even(%s, W)",
        "odd(%s, W)",
        "both(%s, W)",
        "reach(%s, W)",
        "far(%s, W)",
        "hop(%s, W, N)",
        "path(%s, W), path(W, %s)",
    ]

    def _random_graph(self, rng, nodes, density):
        names = ["n%d" % index for index in range(nodes)]
        edges = set()
        for source in names:
            for target in names:
                if rng.random() < density:
                    edges.add((source, target))
        return names, edges

    def test_demand_matches_whole_program_evaluation(self):
        rng = random.Random(4242)
        fired = 0
        checked = 0
        for trial in range(40):
            names, edges = self._random_graph(
                rng, rng.randint(2, 6), rng.random() * 0.6
            )
            facts = "".join("edge(%s, %s)." % pair for pair in sorted(edges))
            for index, rules in enumerate(self.PROGRAMS):
                engine = Engine()
                engine.load(facts + rules)
                defined = {name for name, _ in engine.predicates()}
                for template in self.GOALS:
                    goal = template % tuple(
                        [rng.choice(names)] * template.count("%s")
                    )
                    if goal.split("(")[0] not in defined:
                        continue
                    checked += 1
                    full = engine.query(goal)
                    demand = engine.query(goal, demand=True)
                    fired += demand.stats is not None
                    self.assertEqual(
                        demand.rows,
                        full.rows,
                        "trial %d, program %d, goal %s, edges=%s"
                        % (trial, index, goal, sorted(edges)),
                    )
        self.assertGreater(checked, 500)
        # Guard against the whole suite passing because the transformation
        # silently declined every single time.
        self.assertGreater(fired, checked * 0.5, "the rewrite almost never fired")


if __name__ == "__main__":
    unittest.main()
