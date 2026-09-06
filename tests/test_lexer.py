import unittest

from datalog.errors import ParseError
from datalog.lexer import EOF, IDENT, NUMBER, PUNCT, STRING, VAR, tokenize


def kinds(text):
    return [t.kind for t in tokenize(text)[:-1]]


def values(text):
    return [t.value for t in tokenize(text)[:-1]]


class TestLexer(unittest.TestCase):
    def test_ends_with_eof(self):
        self.assertEqual(tokenize("")[-1].kind, EOF)
        self.assertEqual(tokenize("p(a).")[-1].kind, EOF)

    def test_identifiers_versus_variables(self):
        self.assertEqual(kinds("foo Bar _ _x X1"), [IDENT, VAR, VAR, VAR, VAR])
        self.assertEqual(values("foo Bar _"), ["foo", "Bar", "_"])

    def test_numbers(self):
        self.assertEqual(values("1 2.5 1e3 1.5e-2"), [1, 2.5, 1000.0, 0.015])
        self.assertIsInstance(tokenize("1")[0].value, int)
        self.assertIsInstance(tokenize("1.0")[0].value, float)

    def test_period_after_integer_is_punctuation(self):
        # 'p(3).' must not lex the trailing '.' into the number.
        self.assertEqual(
            kinds("p(3)."), [IDENT, PUNCT, NUMBER, PUNCT, PUNCT]
        )

    def test_strings_and_escapes(self):
        self.assertEqual(values('"hi"'), ["hi"])
        self.assertEqual(values("'hi there'"), ["hi there"])
        self.assertEqual(values(r'"a\nb\t\\ \" c"'), ['a\nb\t\\ " c'])
        self.assertEqual(values(r'"A"'), ["A"])
        self.assertEqual(kinds('"x"'), [STRING])

    def test_multi_character_operators(self):
        self.assertEqual(values(":- ?- != <= >= = < >"), [":-", "?-", "!=", "<=", ">=", "=", "<", ">"])

    def test_comments(self):
        self.assertEqual(values("a // comment\nb"), ["a", "b"])
        self.assertEqual(values("a # comment\nb"), ["a", "b"])
        self.assertEqual(values("a /* c\nd */ b"), ["a", "b"])
        self.assertEqual(values("// only a comment"), [])

    def test_line_and_column_tracking(self):
        tokens = tokenize("p(a).\nq(b).")
        self.assertEqual(tokens[0].line, 1)
        self.assertEqual(tokens[5].line, 2)
        self.assertEqual(tokens[5].col, 1)

    def test_line_tracking_across_block_comment(self):
        tokens = tokenize("a /* one\ntwo\n */ b")
        self.assertEqual(tokens[1].value, "b")
        self.assertEqual(tokens[1].line, 3)

    def test_errors(self):
        for bad in ['"unterminated', "/* unterminated", "p(a) @ b", r'"\q"', r'"\uZZZZ"']:
            with self.assertRaises(ParseError, msg=bad):
                tokenize(bad)

    def test_error_carries_position(self):
        with self.assertRaises(ParseError) as caught:
            tokenize("p(a).\nq(@).")
        self.assertEqual(caught.exception.line, 2)
        self.assertEqual(caught.exception.col, 3)

    def test_source_name_appears_in_message(self):
        with self.assertRaises(ParseError) as caught:
            tokenize("@", "prog.dl")
        self.assertIn("prog.dl", str(caught.exception))


if __name__ == "__main__":
    unittest.main()
