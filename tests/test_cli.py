import builtins
import io
import json
import os
import tempfile
import unittest
from contextlib import redirect_stderr, redirect_stdout

from datalog import cli

PROGRAM = """
edge(a, b). edge(b, c).
path(X, Y) :- edge(X, Y).
path(X, Y) :- edge(X, Z), path(Z, Y).
?- path(a, Where).
"""


class CliTestCase(unittest.TestCase):
    def setUp(self):
        self.directory = tempfile.mkdtemp(prefix="datalog-test-")

    def tearDown(self):
        for name in os.listdir(self.directory):
            os.unlink(os.path.join(self.directory, name))
        os.rmdir(self.directory)

    def write(self, name, text):
        path = os.path.join(self.directory, name)
        with open(path, "w", encoding="utf-8") as handle:
            handle.write(text)
        return path

    def invoke(self, argv):
        out, err = io.StringIO(), io.StringIO()
        with redirect_stdout(out), redirect_stderr(err):
            code = cli.main(argv)
        return code, out.getvalue(), err.getvalue()


class TestRun(CliTestCase):
    def test_runs_queries_from_the_file(self):
        path = self.write("p.dl", PROGRAM)
        code, out, _ = self.invoke(["run", path])
        self.assertEqual(code, 0)
        self.assertIn("?- path(a, Where).", out)
        self.assertIn("Where", out)
        self.assertIn("2 answers.", out)

    def test_extra_query_from_the_command_line(self):
        path = self.write("p.dl", PROGRAM)
        _, out, _ = self.invoke(["run", path, "-q", "path(X, b)"])
        self.assertIn("path(X, b)", out)
        self.assertIn("1 answer.", out)

    def test_ground_query_prints_yes_or_no(self):
        path = self.write("p.dl", PROGRAM)
        _, out, _ = self.invoke(["run", path, "-q", "path(a, c)", "-q", "path(c, a)"])
        self.assertIn("yes.", out)
        self.assertIn("no.", out)

    def test_show_a_relation(self):
        path = self.write("p.dl", PROGRAM)
        _, out, _ = self.invoke(["run", path, "--show", "edge"])
        self.assertIn("edge(a, b).", out)
        self.assertIn("edge/2 (2 tuples)", out)

    def test_show_with_explicit_arity(self):
        path = self.write("p.dl", "p(a). p(b).")
        _, out, _ = self.invoke(["run", path, "--show", "p/1"])
        self.assertIn("p(a).", out)

    def test_show_all(self):
        path = self.write("p.dl", PROGRAM)
        _, out, _ = self.invoke(["run", path, "--show-all"])
        self.assertIn("edge/2", out)
        self.assertIn("path/2", out)

    def test_json_output(self):
        path = self.write("p.dl", PROGRAM)
        _, out, _ = self.invoke(["run", path, "--json", "--show", "path"])
        payload = json.loads(out)
        self.assertEqual(payload["queries"][0]["variables"], ["Where"])
        self.assertEqual(payload["queries"][0]["rows"], [["b"], ["c"]])
        self.assertEqual(len(payload["relations"]["path/2"]), 3)
        self.assertIn("iterations", payload["stats"])

    def test_stats_and_strata_go_to_stderr(self):
        path = self.write("p.dl", PROGRAM)
        _, out, err = self.invoke(["run", path, "--stats", "--strata"])
        self.assertIn("stratum 0", err)
        self.assertIn("rules", err)
        self.assertNotIn("stratum 0", out)

    def test_warn_undefined(self):
        path = self.write("p.dl", "p(X) :- q(X).")
        _, _, err = self.invoke(["run", path, "--warn-undefined"])
        self.assertIn("q/1", err)

    def test_multiple_files_are_combined(self):
        first = self.write("a.dl", "edge(a, b).")
        second = self.write("b.dl", "path(X, Y) :- edge(X, Y). ?- path(A, B).")
        _, out, _ = self.invoke(["run", first, second])
        self.assertIn("1 answer.", out)

    def test_stdin(self):
        import sys

        original = sys.stdin
        sys.stdin = io.StringIO("p(a). ?- p(X).")
        try:
            _, out, _ = self.invoke(["run", "-"])
        finally:
            sys.stdin = original
        self.assertIn("1 answer.", out)

    def test_no_answers_message(self):
        path = self.write("p.dl", "p(a). ?- p(X), X != a.")
        _, out, _ = self.invoke(["run", path])
        self.assertIn("no answers.", out)

    def test_parse_error_is_reported_and_exits_nonzero(self):
        path = self.write("bad.dl", "p(a)\n")
        code, _, err = self.invoke(["run", path])
        self.assertEqual(code, 1)
        self.assertIn("error:", err)
        self.assertIn("bad.dl", err)

    def test_stratification_error_exits_nonzero(self):
        path = self.write("bad.dl", "q(a). p(X) :- q(X), not p(X).")
        code, _, err = self.invoke(["run", path])
        self.assertEqual(code, 1)
        self.assertIn("negatively", err)

    def test_missing_file_exits_nonzero(self):
        code, _, err = self.invoke(["run", os.path.join(self.directory, "nope.dl")])
        self.assertEqual(code, 1)
        self.assertIn("error:", err)

    def test_bad_predicate_spec(self):
        path = self.write("p.dl", "p(a).")
        code, _, err = self.invoke(["run", path, "--show", "p/x"])
        self.assertEqual(code, 1)
        self.assertIn("name/arity", err)

    def test_bad_query_argument(self):
        path = self.write("p.dl", "p(a).")
        code, _, err = self.invoke(["run", path, "-q", "p(X). q(Y)"])
        self.assertEqual(code, 1)
        self.assertIn("error:", err)


class TestCheck(CliTestCase):
    def test_valid_program(self):
        path = self.write("p.dl", PROGRAM)
        code, _, err = self.invoke(["check", path])
        self.assertEqual(code, 0)
        self.assertIn("ok:", err)

    def test_invalid_program(self):
        path = self.write("p.dl", "p(X) :- q(Y).")
        code, _, err = self.invoke(["check", path])
        self.assertEqual(code, 1)
        self.assertIn("error:", err)

    def test_warns_about_undefined_predicates(self):
        path = self.write("p.dl", "p(X) :- q(X).")
        code, _, err = self.invoke(["check", path])
        self.assertEqual(code, 0)
        self.assertIn("q/1", err)


class TestTopLevel(CliTestCase):
    def test_no_command_prints_help(self):
        code, out, _ = self.invoke([])
        self.assertEqual(code, 2)
        self.assertIn("usage", out)

    def test_version(self):
        with self.assertRaises(SystemExit):
            self.invoke(["--version"])


class TestRepl(CliTestCase):
    def drive(self, lines, files=()):
        """Run the REPL over a scripted list of input lines."""
        supply = iter(lines)

        def fake_input(prompt=""):
            try:
                return next(supply)
            except StopIteration:
                raise EOFError

        original = builtins.input
        builtins.input = fake_input
        try:
            return self.invoke(["repl"] + list(files))
        finally:
            builtins.input = original

    def test_add_clauses_and_query(self):
        _, out, _ = self.drive(
            [
                "edge(a, b).",
                "path(X, Y) :- edge(X, Y).",
                "?- path(a, X).",
            ]
        )
        self.assertIn("ok (1 clause)", out)
        self.assertIn("1 answer.", out)

    def test_multi_line_entry(self):
        _, out, _ = self.drive(
            [
                "edge(a, b). edge(b, c).",
                "path(X, Y) :-",
                "    edge(X, Y).",
                "?- path(X, Y).",
            ]
        )
        self.assertIn("2 answers.", out)

    def test_blank_lines_and_unknown_command(self):
        _, out, err = self.drive(["", "   ", ":nosuch"])
        self.assertIn("unknown command", err)

    def test_help_and_list(self):
        _, out, _ = self.drive(["p(a).", ":help", ":list"])
        self.assertIn("Commands", out)
        self.assertIn("p(a).", out)

    def test_list_when_empty(self):
        _, out, _ = self.drive([":list"])
        self.assertIn("no rules loaded", out)

    def test_preds_show_strata_stats(self):
        _, out, _ = self.drive(
            ["p(a).", "q(X) :- p(X).", ":preds", ":show p", ":strata", ":stats"]
        )
        self.assertIn("p/1", out)
        self.assertIn("p(a).", out)
        self.assertIn("stratum 0", out)
        self.assertIn("rules", out)

    def test_show_unknown_relation(self):
        _, out, _ = self.drive([":show nosuch"])
        self.assertIn("(empty)", out)

    def test_show_without_argument(self):
        _, _, err = self.drive([":show"])
        self.assertIn("usage", err)

    def test_reset(self):
        _, out, _ = self.drive(["p(a).", ":reset", ":list"])
        self.assertIn("cleared", out)
        self.assertIn("no rules loaded", out)

    def test_load_command(self):
        path = self.write("p.dl", "p(a). p(b).")
        _, out, _ = self.drive([":load " + path, ":show p"])
        self.assertIn("loaded", out)
        self.assertIn("p(b).", out)

    def test_load_missing_file(self):
        _, _, err = self.drive([":load /nonexistent/file.dl"])
        self.assertIn("error:", err)

    def test_error_recovery_keeps_the_session_alive(self):
        _, out, err = self.drive(
            [
                "p(a).",
                "bad(X) :- q(Y).",   # unsafe: rejected
                "?- p(X).",
            ]
        )
        self.assertIn("error:", err)
        self.assertIn("1 answer.", out)

    def test_stratification_error_is_rolled_back(self):
        _, out, err = self.drive(
            [
                "q(a).",
                "p(X) :- q(X), not p(X).",  # unstratifiable: rejected
                "?- q(X).",
            ]
        )
        self.assertIn("error:", err)
        self.assertIn("1 answer.", out)

    def test_preloaded_files(self):
        path = self.write("p.dl", "p(a). ?- p(X).")
        _, out, _ = self.drive([":list"], files=[path])
        self.assertIn("loaded 1 rules", out)
        self.assertIn("p(a).", out)

    def test_quit(self):
        code, _, _ = self.drive([":quit"])
        self.assertEqual(code, 0)

    def test_keyboard_interrupt_clears_the_buffer(self):
        supply = iter(["p(a"])
        interrupted = {"done": False}

        def fake_input(prompt=""):
            try:
                return next(supply)
            except StopIteration:
                if not interrupted["done"]:
                    interrupted["done"] = True
                    raise KeyboardInterrupt
                raise EOFError

        original = builtins.input
        builtins.input = fake_input
        try:
            code, out, _ = self.invoke(["repl"])
        finally:
            builtins.input = original
        self.assertEqual(code, 0)
        self.assertIn("^C", out)


if __name__ == "__main__":
    unittest.main()
