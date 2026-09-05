"""Keep the documentation honest: run the doctests and the README snippets."""

import doctest
import os
import re
import unittest

import datalog
from datalog import Engine, cli, engine, lexer, parser, safety, stratify, syntax

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
MODULES = [datalog, engine, lexer, parser, safety, stratify, syntax, cli]


def load_tests(loader, tests, ignore):
    for module in MODULES:
        tests.addTests(doctest.DocTestSuite(module))
    return tests


class TestReadme(unittest.TestCase):
    """Every fenced Datalog block in the README must at least load and run."""

    def setUp(self):
        with open(os.path.join(ROOT, "README.md"), "r", encoding="utf-8") as handle:
            self.readme = handle.read()

    def test_datalog_blocks_are_valid(self):
        blocks = re.findall(r"^```prolog\n(.*?)^```", self.readme, re.M | re.S)
        self.assertGreaterEqual(len(blocks), 6, "README lost its ```prolog blocks")
        for block in blocks:
            with self.subTest(block=block.strip()[:60]):
                instance = Engine()
                instance.load(block)
                instance.run()

    def test_readme_example_output_matches(self):
        instance = Engine()
        instance.load(
            "edge(a, b).  edge(b, c).  edge(c, d).\n"
            "path(X, Y) :- edge(X, Y).\n"
            "path(X, Y) :- edge(X, Z), path(Z, Y).\n"
        )
        result = instance.query("path(a, Where)")
        self.assertEqual(result.variables, ["Where"])
        self.assertEqual([row[0] for row in result.rows], ["b", "c", "d"])
        self.assertIn("3 answers.", cli.format_result(result))

    def test_documented_division_behaviour(self):
        instance = Engine()
        instance.load("n(6). n(7). half(X, Y) :- n(X), Y = X / 2.")
        self.assertEqual(instance.relation("half").tuples, {(6, 3), (7, 3.5)})

    def test_documented_cli_flags_exist(self):
        parsed = cli.build_parser().parse_args(
            ["run", "x.dl", "--stats", "--strata", "--warn-undefined", "--json"]
        )
        self.assertTrue(parsed.stats and parsed.strata and parsed.warn_undefined)

    def test_public_api_is_importable(self):
        for name in datalog.__all__:
            self.assertTrue(hasattr(datalog, name), name)


if __name__ == "__main__":
    unittest.main()
