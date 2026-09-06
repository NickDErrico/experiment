"""Tests for derivations -- ``engine.explain``.

A proof is unusually pleasant to test, because a proof can be *checked*.  Most
of this file is one verifier, :func:`verify`, which takes a derivation and
confirms, without knowing anything about how it was produced, that it really is
a proof: every leaf is a base fact of the program, every interior step is a
genuine instance of a real rule whose body holds in the database, and no fact
appears anywhere beneath itself.  That last point is the one that matters most.
A backward search over a recursive program can very easily "prove" ``path(a,
b)`` from ``path(a, b)``, and such a tree looks perfectly convincing until you
check it, which is precisely why the checker is written to be independent of
the searcher rather than sharing its machinery.

With the verifier in hand the interesting tests are differential: explain every
fact a program derives, over random graphs and over every bundled example, and
check every one of the resulting proofs.
"""

import os
import random
import subprocess
import sys
import unittest

from datalog import Engine
from datalog.engine import compare_values
from datalog.errors import DatalogError
from datalog.explain import Condition, Derivation, prove, substitute
from datalog.syntax import Aggregate, Assign, Atom, Compare, Const, Literal, Var

from .test_examples import EXAMPLES


# --------------------------------------------------------------------------
# An independent proof checker
# --------------------------------------------------------------------------


class ProofError(AssertionError):
    """Raised when a derivation is not, in fact, a proof."""


def verify(engine, node, ancestors=()):
    """Check that ``node`` is a genuine derivation.  Returns the fact proved.

    ``ancestors`` are the facts already being proved further up the tree; a
    node that reappears in its own subtree would be circular reasoning, so it
    is rejected.
    """
    if not isinstance(node, Derivation):
        raise ProofError("expected a Derivation, got %r" % (node,))

    fact = _tuple_of(node.atom)
    key = (node.atom.signature, fact)
    if key in ancestors:
        raise ProofError("%s is used in its own derivation" % node.atom)

    relation = engine.relations.get(node.atom.signature)
    if relation is None or fact not in relation.tuples:
        raise ProofError("%s is not in the database" % node.atom)

    if node.rule not in engine.rules:
        raise ProofError("%s is derived by a rule the program does not have" % node.atom)

    head = _instantiate_atom(node.rule.head, node.binding)
    if head != node.atom:
        raise ProofError(
            "rule %s under the recorded bindings yields %s, not %s"
            % (node.rule, head, node.atom)
        )

    if len(node.premises) != len(node.rule.body):
        raise ProofError(
            "%s has %d premises for a body of %d literals"
            % (node.atom, len(node.premises), len(node.rule.body))
        )

    inner = ancestors + (key,)
    for literal, premise in zip(node.rule.body, node.premises):
        _verify_premise(engine, node, literal, premise, inner)
    return key


def _verify_premise(engine, node, literal, premise, ancestors):
    """Check one body literal against the premise offered for it."""
    if isinstance(literal, Literal) and not literal.negated:
        expected = _instantiate_atom(literal.atom, node.binding)
        proved = verify(engine, premise, ancestors)
        if proved != (expected.signature, _tuple_of(expected)):
            raise ProofError(
                "premise for %s proves %s instead" % (expected, premise.atom)
            )
        return

    if not isinstance(premise, Condition):
        raise ProofError("expected a Condition for %s, got %r" % (literal, premise))

    if isinstance(literal, Literal):  # negated
        relation = engine.relations.get(literal.atom.signature)
        pattern = _pattern_of(literal.atom, node.binding)
        if relation is not None and any(_matches(pattern, t) for t in relation.tuples):
            raise ProofError("'%s' is claimed to hold but a matching fact exists" % literal)
        return

    if isinstance(literal, Compare):
        left = _value_of(literal.left, node.binding)
        right = _value_of(literal.right, node.binding)
        if not compare_values(literal.op, left, right):
            raise ProofError("'%s' does not hold under the bindings" % literal)
        return

    if isinstance(literal, Assign):
        if _value_of(literal.var, node.binding) != _value_of(literal.expr, node.binding):
            raise ProofError("'%s' does not hold under the bindings" % literal)
        return

    if isinstance(literal, Aggregate):
        recomputed = engine._aggregate(literal, node.binding)
        if recomputed != node.binding.get(literal.var.name):
            raise ProofError(
                "'%s' evaluates to %r, not %r"
                % (literal, recomputed, node.binding.get(literal.var.name))
            )
        return

    raise ProofError("unexpected body literal %r" % (literal,))


def _tuple_of(atom):
    values = []
    for term in atom.terms:
        if not isinstance(term, Const):
            raise ProofError("%s is not ground" % atom)
        values.append(term.value)
    return tuple(values)


def _instantiate_atom(atom, binding):
    return Atom(atom.pred, tuple(Const(_value_of(t, binding)) for t in atom.terms))


def _pattern_of(atom, binding):
    """Positions of a negated atom that are pinned, as ``(position, value)``."""
    pinned = []
    for position, term in enumerate(atom.terms):
        if isinstance(term, Const):
            pinned.append((position, term.value))
        elif not term.anonymous:
            pinned.append((position, binding[term.name]))
    return pinned


def _matches(pattern, tup):
    return all(tup[position] == value for position, value in pattern)


def _value_of(expr, binding):
    from datalog.engine import _apply_binop

    if isinstance(expr, Const):
        return expr.value
    if isinstance(expr, Var):
        if expr.name not in binding:
            raise ProofError("variable %s is not bound by the derivation" % expr.name)
        return binding[expr.name]
    if hasattr(expr, "operand"):
        value = _value_of(expr.operand, binding)
        return -value if expr.op == "-" else value
    return _apply_binop(
        expr.op, _value_of(expr.left, binding), _value_of(expr.right, binding)
    )


class VerifierTest(unittest.TestCase):
    """The checker is only worth anything if it rejects a bad proof."""

    def setUp(self):
        self.engine = Engine()
        self.engine.load(
            """
            edge(a, b).  edge(b, a).
            path(X, Y) :- edge(X, Y).
            path(X, Y) :- edge(X, Z), path(Z, Y).
            """
        )
        self.good = self.engine.explain("path(a, a)")

    def test_accepts_a_real_derivation(self):
        verify(self.engine, self.good)

    def test_rejects_a_circular_derivation(self):
        # Hand-build the tempting nonsense: path(a, a) because path(a, a).
        rule = next(r for r in self.engine.rules if len(r.body) == 2)
        circular = Derivation(
            atom=Atom("path", (Const("a"), Const("a"))),
            rule=rule,
            binding={"X": "a", "Y": "a", "Z": "a"},
            premises=(None, None),
        )
        circular = Derivation(
            atom=circular.atom,
            rule=rule,
            binding={"X": "a", "Y": "a", "Z": "b"},
            premises=(
                Derivation(
                    atom=Atom("edge", (Const("a"), Const("b"))),
                    rule=next(r for r in self.engine.rules if not r.body),
                    binding={},
                ),
                circular,
            ),
        )
        with self.assertRaises(ProofError):
            verify(self.engine, circular)

    def test_rejects_a_fact_that_is_not_in_the_database(self):
        bogus = Derivation(
            atom=Atom("path", (Const("a"), Const("zzz"))),
            rule=next(r for r in self.engine.rules if not r.body),
            binding={},
        )
        with self.assertRaises(ProofError):
            verify(self.engine, bogus)

    def test_rejects_bindings_that_do_not_yield_the_head(self):
        bad = Derivation(
            atom=self.good.atom,
            rule=self.good.rule,
            binding=dict(self.good.binding, Y="b"),
            premises=self.good.premises,
        )
        with self.assertRaises(ProofError):
            verify(self.engine, bad)


# --------------------------------------------------------------------------
# Shape of a derivation
# --------------------------------------------------------------------------


class DerivationTest(unittest.TestCase):
    def setUp(self):
        self.engine = Engine()
        self.engine.load(
            """
            edge(a, b).  edge(b, c).  edge(c, d).
            path(X, Y) :- edge(X, Y).
            path(X, Y) :- edge(X, Z), path(Z, Y).
            """
        )

    def test_renders_a_chain(self):
        self.assertEqual(
            str(self.engine.explain("path(a, d)")).splitlines(),
            [
                "path(a, d)   by  path(X, Y) :- edge(X, Z), path(Z, Y).",
                "├─ edge(a, b)",
                "└─ path(b, d)   by  path(X, Y) :- edge(X, Z), path(Z, Y).",
                "   ├─ edge(b, c)",
                "   └─ path(c, d)   by  path(X, Y) :- edge(X, Y).",
                "      └─ edge(c, d)",
            ],
        )

    def test_a_base_fact_is_a_leaf(self):
        derivation = self.engine.explain("edge(a, b)")
        self.assertTrue(derivation.is_fact)
        self.assertEqual(derivation.premises, ())
        self.assertEqual(str(derivation), "edge(a, b)")
        self.assertEqual(derivation.depth, 0)

    def test_undeliverable_facts_have_no_derivation(self):
        self.assertIsNone(self.engine.explain("path(d, a)"))
        self.assertIsNone(self.engine.explain("edge(zz, yy)"))

    def test_unknown_predicate_has_no_derivation(self):
        self.assertIsNone(self.engine.explain("nosuch(a)"))

    def test_depth_support_and_rules(self):
        derivation = self.engine.explain("path(a, d)")
        self.assertEqual(derivation.depth, 3)
        self.assertEqual(
            [str(atom) for atom in derivation.support()],
            ["edge(a, b)", "edge(b, c)", "edge(c, d)"],
        )
        self.assertEqual(
            sorted(str(rule) for rule in derivation.rules_used()),
            [
                "path(X, Y) :- edge(X, Y).",
                "path(X, Y) :- edge(X, Z), path(Z, Y).",
            ],
        )

    def test_walk_visits_every_node(self):
        derivation = self.engine.explain("path(a, d)")
        self.assertEqual(len(list(derivation.walk())), 6)

    def test_to_dict_is_json_shaped(self):
        payload = self.engine.explain("path(c, d)").to_dict()
        self.assertEqual(payload["fact"], "path(c, d)")
        self.assertEqual(payload["rule"], "path(X, Y) :- edge(X, Y).")
        self.assertEqual(payload["premises"], [{"fact": "edge(c, d)"}])

    def test_accepts_an_atom_as_well_as_text(self):
        atom = Atom("path", (Const("a"), Const("c")))
        self.assertEqual(str(self.engine.explain(atom).atom), "path(a, c)")

    def test_a_non_ground_goal_is_rejected(self):
        with self.assertRaises(DatalogError) as caught:
            self.engine.explain("path(a, X)")
        self.assertIn("ground", str(caught.exception))
        self.assertIn("X", str(caught.exception))

    def test_garbage_goals_are_rejected(self):
        for goal in ["path(a, b), edge(a, b)", "path(X, Y) :- edge(X, Y)", 17]:
            with self.assertRaises(DatalogError):
                self.engine.explain(goal)

    def test_a_derivable_base_fact_is_explained_as_a_fact(self):
        engine = Engine()
        engine.load(
            """
            edge(a, b).  edge(b, c).  edge(a, c).
            edge(X, Y) :- edge(X, Z), edge(Z, Y).
            """
        )
        # edge(a, c) is written down *and* derivable; the simpler answer wins.
        self.assertTrue(engine.explain("edge(a, c)").is_fact)


class DeterminismTest(unittest.TestCase):
    """The same fact must always be explained the same way.

    Several derivations usually exist, and picking whichever one a set happens
    to yield first would make the output depend on the process's hash seed --
    invisible in any single run, and maddening when two runs disagree.  Only
    separate interpreters can see this, so this test starts some.
    """

    PROGRAM = """
        edge(a, b).  edge(a, c).  edge(b, d).  edge(c, d).  edge(d, e).
        edge(e, a).
        path(X, Y) :- edge(X, Y).
        path(X, Y) :- edge(X, Z), path(Z, Y).
    """

    def test_output_does_not_depend_on_the_hash_seed(self):
        script = (
            "import sys; from datalog import Engine\n"
            "e = Engine()\n"
            "e.load(%r)\n"
            "print(e.explain('path(a, e)'))\n" % self.PROGRAM
        )
        seen = set()
        root = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
        for seed in ("0", "1", "12345"):
            environment = dict(os.environ, PYTHONHASHSEED=seed, PYTHONPATH=root)
            finished = subprocess.run(
                [sys.executable, "-c", script],
                capture_output=True,
                text=True,
                env=environment,
                cwd=root,
            )
            self.assertEqual(finished.returncode, 0, finished.stderr)
            seen.add(finished.stdout)
        self.assertEqual(len(seen), 1, "explain output varies with the hash seed:\n%s"
                         % "\n--- vs ---\n".join(sorted(seen)))


class ShortestDerivationTest(unittest.TestCase):
    def test_the_proof_is_a_shortest_one(self):
        # Both a one-step and a two-step route to path(a, c) exist.
        engine = Engine()
        engine.load(
            """
            edge(a, b).  edge(b, c).  edge(a, c).
            path(X, Y) :- edge(X, Y).
            path(X, Y) :- edge(X, Z), path(Z, Y).
            """
        )
        self.assertEqual(engine.explain("path(a, c)").depth, 1)


# --------------------------------------------------------------------------
# The literals that are not atoms
# --------------------------------------------------------------------------


class ConditionTest(unittest.TestCase):
    def test_negation_reports_that_nothing_matched(self):
        engine = Engine()
        engine.load(
            """
            parent(alice, bob).  parent(bob, carol).
            root(X) :- parent(X, _), not parent(_, X).
            """
        )
        lines = str(engine.explain("root(alice)")).splitlines()
        self.assertEqual(lines[1], "├─ parent(alice, bob)")
        self.assertEqual(lines[2], "└─ not parent(_, alice)   (no such fact)")

    def test_comparisons_are_shown_with_their_values(self):
        engine = Engine()
        engine.load("age(bob, 20).  adult(P) :- age(P, A), A >= 18.")
        self.assertIn("20 >= 18", str(engine.explain("adult(bob)")))

    def test_assignments_are_shown_with_their_values(self):
        engine = Engine()
        engine.load("num(3).  next(Y) :- num(X), Y = X + 1.")
        self.assertIn("4 = (3 + 1)", str(engine.explain("next(4)")))

    def test_aggregates_keep_their_local_variables(self):
        engine = Engine()
        engine.load(
            """
            dept(eng).
            employee(ann, eng).  employee(bo, eng).
            salary(ann, 100).    salary(bo, 200).
            payroll(D, T) :- dept(D), T = sum S { employee(E, D), salary(E, S) }.
            """
        )
        derivation = engine.explain("payroll(eng, 300)")
        # The group key is substituted, the aggregated variables are not.
        self.assertIn(
            "300 = sum S { employee(E, eng), salary(E, S) }", str(derivation)
        )
        verify(engine, derivation)

    def test_anonymous_variables_are_not_substituted(self):
        engine = Engine()
        engine.load("edge(a, b).  node(X) :- edge(X, _).")
        self.assertIn("edge(a, b)", str(engine.explain("node(a)")))

    def test_substitute_leaves_unbound_variables_alone(self):
        literal = Compare(">", Var("A"), Var("B"))
        self.assertEqual(str(substitute(literal, {"A": 5})), "5 > B")


# --------------------------------------------------------------------------
# Tracking
# --------------------------------------------------------------------------


class TrackingTest(unittest.TestCase):
    def test_tracking_is_off_until_asked_for(self):
        engine = Engine()
        engine.load("edge(a, b).")
        engine.run()
        self.assertEqual(engine.relation("edge").rounds, {})

        engine.explain("edge(a, b)")
        self.assertTrue(engine.track_derivations)
        self.assertEqual(len(engine.relation("edge").rounds), 1)

    def test_tracking_can_be_asked_for_up_front(self):
        engine = Engine(track_derivations=True)
        engine.load("edge(a, b).")
        engine.run()
        self.assertEqual(len(engine.relation("edge").rounds), 1)

    def test_proving_without_tracking_says_so(self):
        engine = Engine()
        engine.load("edge(a, b).")
        engine.run()
        with self.assertRaises(DatalogError) as caught:
            prove(engine, Atom("edge", (Const("a"), Const("b"))))
        self.assertIn("track_derivations", str(caught.exception))

    def test_rounds_increase_with_derivation_depth(self):
        engine = Engine(track_derivations=True)
        engine.load(
            """
            edge(a, b).  edge(b, c).  edge(c, d).
            path(X, Y) :- edge(X, Y).
            path(X, Y) :- edge(X, Z), path(Z, Y).
            """
        )
        engine.run()
        rounds = engine.relation("path").rounds
        self.assertLess(rounds[("b", "c")], rounds[("a", "c")])
        self.assertLess(rounds[("a", "c")], rounds[("a", "d")])

    def test_adding_a_rule_keeps_tracking_on(self):
        engine = Engine()
        engine.load("edge(a, b).  path(X, Y) :- edge(X, Y).")
        engine.explain("path(a, b)")
        engine.load("edge(b, c).")
        self.assertIsNotNone(engine.explain("path(b, c)"))

    def test_explaining_does_not_disturb_the_relations(self):
        engine = Engine()
        engine.load(
            """
            edge(a, b).  edge(b, c).
            path(X, Y) :- edge(X, Y).
            path(X, Y) :- edge(X, Z), path(Z, Y).
            """
        )
        before = set(engine.relation("path").tuples)
        engine.explain("path(a, c)")
        self.assertEqual(set(engine.relation("path").tuples), before)


# --------------------------------------------------------------------------
# Differential: explain everything, check every proof
# --------------------------------------------------------------------------


def explain_everything(test, engine):
    """Explain every derived tuple of every relation, and verify each proof."""
    engine.track_derivations = True
    engine.run(force=True)
    checked = 0
    for (name, arity), relation in sorted(engine.relations.items()):
        for tup in sorted(relation.tuples, key=lambda t: [str(v) for v in t]):
            atom = Atom(name, tuple(Const(value) for value in tup))
            derivation = engine.explain(atom)
            test.assertIsNotNone(derivation, "no derivation for %s" % atom)
            try:
                verify(engine, derivation)
            except ProofError as exc:
                test.fail("bad derivation for %s: %s\n%s" % (atom, exc, derivation))
            checked += 1
    return checked


class RandomGraphTest(unittest.TestCase):
    """Over random graphs -- cycles very much included -- every fact of the
    transitive closure must have a checkable, non-circular proof."""

    def test_random_reachability(self):
        rng = random.Random(20260906)
        total = 0
        for _ in range(25):
            size = rng.randint(2, 7)
            edges = {
                (rng.randrange(size), rng.randrange(size))
                for _ in range(rng.randint(1, size * 2))
            }
            program = "".join("edge(n%d, n%d)." % pair for pair in sorted(edges))
            engine = Engine()
            engine.load(
                program
                + """
                path(X, Y) :- edge(X, Y).
                path(X, Y) :- edge(X, Z), path(Z, Y).
                """
            )
            total += explain_everything(self, engine)
        self.assertGreater(total, 200, "the random programs derived almost nothing")

    def test_random_program_with_negation_and_arithmetic(self):
        rng = random.Random(4711)
        for _ in range(15):
            size = rng.randint(2, 6)
            facts = "".join(
                "num(%d)." % rng.randrange(20) for _ in range(rng.randint(2, 8))
            )
            facts += "".join(
                "link(n%d, n%d)." % (rng.randrange(size), rng.randrange(size))
                for _ in range(rng.randint(1, size * 2))
            )
            engine = Engine()
            engine.load(
                facts
                + """
                node(X) :- link(X, _).
                node(Y) :- link(_, Y).
                reach(X, Y) :- link(X, Y).
                reach(X, Y) :- link(X, Z), reach(Z, Y).
                source(X) :- node(X), not link(_, X).
                big(N) :- num(N), N > 9.
                doubled(M) :- num(N), M = N * 2.
                fanout(X, C) :- node(X), C = count { link(X, _) }.
                """
            )
            explain_everything(self, engine)


class ExampleProgramTest(unittest.TestCase):
    """Every fact every bundled example derives must have a valid proof."""

    def test_every_example(self):
        names = sorted(n for n in os.listdir(EXAMPLES) if n.endswith(".dl"))
        self.assertTrue(names, "no examples found")
        for name in names:
            with self.subTest(example=name):
                path = os.path.join(EXAMPLES, name)
                with open(path, "r", encoding="utf-8") as handle:
                    source = handle.read()
                engine = Engine()
                engine.load(source, name)
                self.assertGreater(explain_everything(self, engine), 0)


if __name__ == "__main__":
    unittest.main()
