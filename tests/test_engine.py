import random
import unittest
from collections import defaultdict

from datalog import Engine, solve
from datalog.engine import compare_values, sort_key
from datalog.errors import DatalogError, EvaluationError
from datalog.stratify import stratify


def relations(engine):
    """Snapshot every relation as a plain dict of sets, for comparison."""
    return {sig: set(rel.tuples) for sig, rel in engine.relations.items()}


def evaluate_naively(source):
    """An independent, deliberately dumb evaluator used as a reference.

    It re-fires every rule over the whole database until nothing changes, with
    no delta tracking at all.  Semi-naive evaluation must agree with it exactly;
    if it does not, the delta bookkeeping is wrong.
    """
    engine = Engine()
    engine.load(source)
    engine.strata, engine.stratum_of = stratify(engine.rules)
    engine.relations = {}
    for signature in engine.stratum_of:
        engine._relation(signature)

    by_stratum = defaultdict(list)
    for rule in engine.rules:
        by_stratum[engine.stratum_of[rule.head.signature]].append(rule)

    for level in range(len(engine.strata)):
        while True:
            produced = defaultdict(set)
            for rule in by_stratum.get(level, []):
                engine._fire(rule, produced, None, None)
            if not any(produced.values()):
                break
            for signature, tuples in produced.items():
                engine._relation(signature).update(tuples)
    engine._dirty = False
    return relations(engine)


def transitive_closure(edges):
    """Reference transitive closure computed by repeated BFS."""
    successors = defaultdict(set)
    for source, target in edges:
        successors[source].add(target)
    closure = set()
    for start in {node for edge in edges for node in edge}:
        seen = set()
        stack = list(successors[start])
        while stack:
            node = stack.pop()
            if node in seen:
                continue
            seen.add(node)
            closure.add((start, node))
            stack.extend(successors[node])
    return closure


class TestBasicEvaluation(unittest.TestCase):
    def test_facts_only(self):
        engine = Engine()
        engine.load("p(a). p(b). q(1, 2).")
        self.assertEqual(engine.relation("p").tuples, {("a",), ("b",)})
        self.assertEqual(engine.relation("q").tuples, {(1, 2)})

    def test_transitive_closure(self):
        engine = Engine()
        engine.load(
            """
            edge(a, b). edge(b, c). edge(c, d).
            path(X, Y) :- edge(X, Y).
            path(X, Y) :- edge(X, Z), path(Z, Y).
            """
        )
        self.assertEqual(
            engine.relation("path").tuples,
            {
                ("a", "b"), ("b", "c"), ("c", "d"),
                ("a", "c"), ("b", "d"), ("a", "d"),
            },
        )

    def test_cyclic_graph_terminates(self):
        engine = Engine()
        engine.load(
            """
            edge(a, b). edge(b, c). edge(c, a).
            path(X, Y) :- edge(X, Y).
            path(X, Y) :- path(X, Z), path(Z, Y).
            """
        )
        nodes = ["a", "b", "c"]
        self.assertEqual(
            engine.relation("path").tuples,
            {(x, y) for x in nodes for y in nodes},
        )

    def test_repeated_variable_in_atom(self):
        engine = Engine()
        engine.load("p(a, a). p(a, b). p(b, b). same(X) :- p(X, X).")
        self.assertEqual(engine.relation("same").tuples, {("a",), ("b",)})

    def test_zero_arity_predicates(self):
        engine = Engine()
        engine.load("ready. go :- ready. stop :- not ready.")
        self.assertEqual(engine.relation("go", 0).tuples, {()})
        self.assertEqual(engine.relation("stop", 0).tuples, set())

    def test_constants_in_rule_head(self):
        engine = Engine()
        engine.load("n(1). n(2). tagged(small, X) :- n(X), X < 2.")
        self.assertEqual(engine.relation("tagged").tuples, {("small", 1)})

    def test_mutual_recursion(self):
        engine = Engine()
        engine.load(
            """
            num(0). num(1). num(2). num(3). num(4).
            succ(0, 1). succ(1, 2). succ(2, 3). succ(3, 4).
            even(0).
            even(X) :- succ(Y, X), odd(Y).
            odd(X)  :- succ(Y, X), even(Y).
            """
        )
        self.assertEqual(engine.relation("even").tuples, {(0,), (2,), (4,)})
        self.assertEqual(engine.relation("odd").tuples, {(1,), (3,)})

    def test_same_generation(self):
        engine = Engine()
        engine.load(
            """
            up(a, x). up(b, x). up(c, y).
            flat(x, y).
            down(y, d). down(y, e).
            sg(X, Y) :- flat(X, Y).
            sg(X, Y) :- up(X, A), sg(A, B), down(B, Y).
            """
        )
        self.assertEqual(
            engine.relation("sg").tuples,
            {("x", "y"), ("a", "d"), ("a", "e"), ("b", "d"), ("b", "e")},
        )

    def test_reevaluation_is_idempotent(self):
        engine = Engine()
        engine.load("e(a, b). p(X, Y) :- e(X, Y).")
        engine.run()
        first = relations(engine)
        engine.run(force=True)
        self.assertEqual(relations(engine), first)


class TestNegation(unittest.TestCase):
    def test_simple_negation(self):
        engine = Engine()
        engine.load(
            """
            person(alice). person(bob).
            employed(alice).
            jobless(X) :- person(X), not employed(X).
            """
        )
        self.assertEqual(engine.relation("jobless").tuples, {("bob",)})

    def test_negation_over_a_recursive_relation(self):
        engine = Engine()
        engine.load(
            """
            node(a). node(b). node(c). node(d).
            edge(a, b). edge(b, c).
            path(X, Y) :- edge(X, Y).
            path(X, Y) :- edge(X, Z), path(Z, Y).
            unreachable(X) :- node(X), not path(a, X).
            """
        )
        self.assertEqual(engine.relation("unreachable").tuples, {("a",), ("d",)})

    def test_anonymous_variable_under_negation_is_existential(self):
        engine = Engine()
        engine.load(
            """
            n(1). n(2). n(3).
            r(1, x). r(3, y).
            bare(X) :- n(X), not r(X, _).
            """
        )
        self.assertEqual(engine.relation("bare").tuples, {(2,)})

    def test_double_negation_stratifies(self):
        engine = Engine()
        engine.load(
            """
            n(a). n(b). n(c).
            p(a).
            q(X) :- n(X), not p(X).
            r(X) :- n(X), not q(X).
            """
        )
        self.assertEqual(engine.relation("r").tuples, {("a",)})


class TestArithmeticAndComparison(unittest.TestCase):
    def test_arithmetic(self):
        engine = Engine()
        engine.load(
            """
            n(6). n(7).
            plus(X, Y)  :- n(X), Y = X + 1.
            minus(X, Y) :- n(X), Y = X - 1.
            times(X, Y) :- n(X), Y = X * 2.
            half(X, Y)  :- n(X), Y = X / 2.
            rem(X, Y)   :- n(X), Y = X % 4.
            neg(X, Y)   :- n(X), Y = -X.
            """
        )
        self.assertEqual(engine.relation("plus").tuples, {(6, 7), (7, 8)})
        self.assertEqual(engine.relation("minus").tuples, {(6, 5), (7, 6)})
        self.assertEqual(engine.relation("times").tuples, {(6, 12), (7, 14)})
        # Exact integer division stays an int; inexact becomes a float.
        self.assertEqual(engine.relation("half").tuples, {(6, 3), (7, 3.5)})
        self.assertEqual(engine.relation("rem").tuples, {(6, 2), (7, 3)})
        self.assertEqual(engine.relation("neg").tuples, {(6, -6), (7, -7)})

    def test_string_concatenation(self):
        engine = Engine()
        engine.load('w("ab"). w("cd"). j(Z) :- w(X), w(Y), X < Y, Z = X + Y.')
        self.assertEqual(engine.relation("j").tuples, {("abcd",)})

    def test_division_by_zero(self):
        engine = Engine()
        engine.load("n(1). p(Y) :- n(X), Y = X / 0.")
        with self.assertRaises(EvaluationError):
            engine.run()

    def test_type_error_in_arithmetic(self):
        engine = Engine()
        engine.load("n(a). p(Y) :- n(X), Y = X + 1.")
        with self.assertRaises(EvaluationError):
            engine.run()

    def test_comparison_operators(self):
        engine = Engine()
        engine.load(
            """
            n(1). n(2). n(3).
            lt(X)  :- n(X), X < 2.
            le(X)  :- n(X), X <= 2.
            gt(X)  :- n(X), X > 2.
            ge(X)  :- n(X), X >= 2.
            ne(X)  :- n(X), X != 2.
            eq(X)  :- n(X), X = 2.
            """
        )
        self.assertEqual(engine.relation("lt").tuples, {(1,)})
        self.assertEqual(engine.relation("le").tuples, {(1,), (2,)})
        self.assertEqual(engine.relation("gt").tuples, {(3,)})
        self.assertEqual(engine.relation("ge").tuples, {(2,), (3,)})
        self.assertEqual(engine.relation("ne").tuples, {(1,), (3,)})
        self.assertEqual(engine.relation("eq").tuples, {(2,)})

    def test_total_order_mixes_numbers_and_strings(self):
        # Ordering must never raise, even across types.
        self.assertTrue(compare_values("<", 1, "a"))
        self.assertFalse(compare_values("<", "a", 1))
        self.assertTrue(compare_values("=", 1, 1.0))
        self.assertEqual(sorted([1, "a", 2.5], key=sort_key), [1, 2.5, "a"])

    def test_equality_binds_in_both_directions(self):
        engine = Engine()
        engine.load("n(1). p(X, Y) :- n(X), Y = X. q(X, Y) :- n(Y), Y = X.")
        self.assertEqual(engine.relation("p").tuples, {(1, 1)})
        self.assertEqual(engine.relation("q").tuples, {(1, 1)})

    def test_literals_are_reordered_to_be_runnable(self):
        engine = Engine()
        engine.load("n(1). n(5). p(X, Y) :- X < Y, n(X), n(Y).")
        self.assertEqual(engine.relation("p").tuples, {(1, 5)})


class TestQueries(unittest.TestCase):
    def setUp(self):
        self.engine = Engine()
        self.engine.load(
            """
            edge(a, b). edge(b, c).
            path(X, Y) :- edge(X, Y).
            path(X, Y) :- edge(X, Z), path(Z, Y).
            """
        )

    def test_query_from_text(self):
        result = self.engine.query("path(a, X)")
        self.assertEqual(result.variables, ["X"])
        self.assertEqual(result.rows, [("b",), ("c",)])

    def test_query_accepts_full_syntax(self):
        self.assertEqual(
            self.engine.query("?- path(a, X).").rows, [("b",), ("c",)]
        )

    def test_ground_query(self):
        yes = self.engine.query("path(a, c)")
        no = self.engine.query("path(c, a)")
        self.assertTrue(yes.is_ground and bool(yes))
        self.assertTrue(no.is_ground and not bool(no))

    def test_query_variable_order_follows_the_source(self):
        result = self.engine.query("path(Y, X)")
        self.assertEqual(result.variables, ["Y", "X"])

    def test_query_iteration_yields_dicts(self):
        rows = list(self.engine.query("path(a, X)"))
        self.assertEqual(rows, [{"X": "b"}, {"X": "c"}])

    def test_query_deduplicates(self):
        engine = Engine()
        engine.load("p(a, 1). p(a, 2). p(b, 3).")
        self.assertEqual(engine.query("p(X, _)").rows, [("a",), ("b",)])

    def test_query_with_comparison_and_negation(self):
        engine = Engine()
        engine.load("n(1). n(2). n(3). skip(2).")
        result = engine.query("n(X), not skip(X), X > 1")
        self.assertEqual(result.rows, [(3,)])

    def test_query_on_unknown_predicate_is_empty(self):
        self.assertEqual(self.engine.query("nosuch(X)").rows, [])

    def test_solve_helper(self):
        engine, results = solve("p(a). p(b). ?- p(X).")
        self.assertEqual(len(results), 1)
        self.assertEqual(results[0][1].rows, [("a",), ("b",)])


class TestEngineHousekeeping(unittest.TestCase):
    def test_arity_conflict_rejected(self):
        engine = Engine()
        engine.load("p(a).")
        with self.assertRaises(DatalogError):
            engine.load("p(a, b).")

    def test_relation_requires_arity_when_ambiguous(self):
        engine = Engine()
        engine.load("p(a). q(X) :- p(X). r(X, Y) :- p(X), p(Y).")
        engine.run()
        # Force an ambiguous name by registering two arities for one name.
        engine.relations[("amb", 1)] = engine._relation(("amb", 1))
        engine.relations[("amb", 2)] = engine._relation(("amb", 2))
        with self.assertRaises(DatalogError):
            engine.relation("amb")
        self.assertEqual(len(engine.relation("amb", 1)), 0)

    def test_unknown_relation_is_empty(self):
        self.assertEqual(len(Engine().relation("nope")), 0)

    def test_undefined_predicates_reported(self):
        engine = Engine()
        engine.load("p(X) :- q(X), not r(X).")
        self.assertEqual(engine.undefined_predicates(), [("q", 1), ("r", 1)])

    def test_reset(self):
        engine = Engine()
        engine.load("p(a).")
        engine.run()
        engine.reset()
        self.assertEqual(engine.rules, [])
        self.assertEqual(len(engine.relation("p")), 0)

    def test_truncate_rules_restores_arity_table(self):
        engine = Engine()
        engine.load("p(a).")
        engine.load("q(a, b).")
        engine.truncate_rules(1)
        self.assertEqual(len(engine.rules), 1)
        engine.load("q(a, b, c).")  # the old q/2 must no longer conflict
        self.assertEqual(len(engine.rules), 2)

    def test_stats_are_populated(self):
        engine = Engine()
        engine.load("e(a, b). p(X, Y) :- e(X, Y).")
        engine.run()
        self.assertEqual(engine.stats["rules"], 2)
        self.assertGreaterEqual(engine.stats["iterations"], 1)
        self.assertEqual(engine.stats["tuples"], 2)

    def test_iteration_guard_stops_runaway_arithmetic(self):
        engine = Engine(max_iterations=50)
        engine.load("p(1). p(Y) :- p(X), Y = X + 1.")
        with self.assertRaises(EvaluationError) as caught:
            engine.run()
        self.assertIn("fixpoint", str(caught.exception))

    def test_tuple_guard_stops_runaway_growth(self):
        engine = Engine(max_tuples=100)
        engine.load("p(1). p(Y) :- p(X), Y = X + 1, Y < 100000.")
        with self.assertRaises(EvaluationError) as caught:
            engine.run()
        self.assertIn("tuples", str(caught.exception))

    def test_empty_program(self):
        engine = Engine()
        engine.run()
        self.assertEqual(engine.strata, [])
        self.assertEqual(engine.query("p(X)").rows, [])


class TestAgainstReferenceImplementations(unittest.TestCase):
    """Differential tests: the engine must agree with simpler evaluators."""

    LINEAR = """
        path(X, Y) :- edge(X, Y).
        path(X, Y) :- edge(X, Z), path(Z, Y).
    """
    NONLINEAR = """
        path(X, Y) :- edge(X, Y).
        path(X, Y) :- path(X, Z), path(Z, Y).
    """
    RIGHT_LINEAR = """
        path(X, Y) :- edge(X, Y).
        path(X, Y) :- path(X, Z), edge(Z, Y).
    """

    def _random_graph(self, rng, nodes, density):
        names = ["n%d" % i for i in range(nodes)]
        edges = set()
        for source in names:
            for target in names:
                if rng.random() < density:
                    edges.add((source, target))
        return edges

    def test_transitive_closure_matches_bfs_reference(self):
        rng = random.Random(20240607)
        for trial in range(25):
            edges = self._random_graph(rng, rng.randint(1, 7), rng.random() * 0.5)
            facts = "".join("edge(%s, %s)." % pair for pair in edges)
            expected = transitive_closure(edges)
            for name, rules in (
                ("linear", self.LINEAR),
                ("nonlinear", self.NONLINEAR),
                ("right-linear", self.RIGHT_LINEAR),
            ):
                engine = Engine()
                engine.load(facts + rules)
                self.assertEqual(
                    engine.relation("path").tuples,
                    expected,
                    "trial %d, %s rules, edges=%s" % (trial, name, sorted(edges)),
                )

    def test_semi_naive_matches_naive_on_random_programs(self):
        rng = random.Random(981)
        programs = [
            self.LINEAR,
            self.NONLINEAR,
            self.RIGHT_LINEAR,
            """
            path(X, Y) :- edge(X, Y).
            path(X, Y) :- edge(X, Z), path(Z, Y).
            node(X) :- edge(X, _).
            node(Y) :- edge(_, Y).
            isolated(X) :- node(X), not path(X, _).
            cyclic(X) :- path(X, X).
            acyclic(X) :- node(X), not cyclic(X).
            """,
            """
            node(X) :- edge(X, _).
            node(Y) :- edge(_, Y).
            path(X, Y) :- edge(X, Y).
            path(X, Y) :- path(X, Z), path(Z, Y).
            degree(X, N) :- node(X), N = count { edge(X, _) }.
            reach(X, N) :- node(X), N = count { path(X, _) }.
            """,
        ]
        for trial in range(20):
            edges = self._random_graph(rng, rng.randint(1, 6), rng.random() * 0.6)
            facts = "".join("edge(%s, %s)." % pair for pair in edges)
            for index, rules in enumerate(programs):
                source = facts + rules
                engine = Engine()
                engine.load(source)
                engine.run()
                self.assertEqual(
                    relations(engine),
                    evaluate_naively(source),
                    "trial %d, program %d, edges=%s"
                    % (trial, index, sorted(edges)),
                )


if __name__ == "__main__":
    unittest.main()
