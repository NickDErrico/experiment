"""Hand-written tokenizer for the Datalog surface syntax.

Lexical conventions
-------------------
* ``//`` and ``#`` start a line comment; ``/* ... */`` is a block comment.
* Identifiers starting with a lowercase letter are predicate names or symbols.
* Identifiers starting with an uppercase letter or ``_`` are variables.
* ``"..."`` and ``'...'`` both produce string constants.
* Numbers are integers or floats (``1``, ``2.5``, ``1e3``).
"""

from __future__ import annotations

import re

from .errors import ParseError

IDENT = "IDENT"
VAR = "VAR"
NUMBER = "NUMBER"
STRING = "STRING"
PUNCT = "PUNCT"
EOF = "EOF"

_IDENT_RE = re.compile(r"[a-z][A-Za-z0-9_]*")
_VAR_RE = re.compile(r"[A-Z_][A-Za-z0-9_]*")
_NUMBER_RE = re.compile(r"\d+(?:\.\d+)?(?:[eE][+-]?\d+)?")

# Longest operators first so that ``<=`` never lexes as ``<`` then ``=``.
_OPERATORS = (
    ":-",
    "?-",
    "!=",
    "<=",
    ">=",
    "(",
    ")",
    "{",
    "}",
    "[",
    "]",
    ",",
    ";",
    ".",
    "=",
    "<",
    ">",
    "+",
    "-",
    "*",
    "/",
    "%",
    "!",
    ":",
)

_ESCAPES = {
    "n": "\n",
    "t": "\t",
    "r": "\r",
    "0": "\0",
    "\\": "\\",
    '"': '"',
    "'": "'",
}


class Token:
    """A single lexical token, with the coordinates needed for diagnostics."""

    __slots__ = ("kind", "value", "line", "col")

    def __init__(self, kind, value, line, col):
        self.kind = kind
        self.value = value
        self.line = line
        self.col = col

    def __repr__(self):
        return "Token(%s, %r, line=%d, col=%d)" % (
            self.kind,
            self.value,
            self.line,
            self.col,
        )

    def __eq__(self, other):
        if not isinstance(other, Token):
            return NotImplemented
        return self.kind == other.kind and self.value == other.value


def tokenize(text, source_name=None):
    """Turn ``text`` into a list of tokens terminated by an ``EOF`` token."""
    tokens = []
    i = 0
    line = 1
    line_start = 0
    n = len(text)

    def col(pos):
        return pos - line_start + 1

    while i < n:
        ch = text[i]

        if ch == "\n":
            line += 1
            i += 1
            line_start = i
            continue
        if ch in " \t\r\f\v":
            i += 1
            continue

        # Comments -------------------------------------------------------
        if ch == "#" or text.startswith("//", i):
            newline = text.find("\n", i)
            i = n if newline == -1 else newline
            continue
        if text.startswith("/*", i):
            end = text.find("*/", i + 2)
            if end == -1:
                raise ParseError("unterminated block comment", line, col(i), source_name)
            line += text.count("\n", i, end)
            last_nl = text.rfind("\n", i, end)
            if last_nl != -1:
                line_start = last_nl + 1
            i = end + 2
            continue

        # Strings --------------------------------------------------------
        if ch == '"' or ch == "'":
            value, i = _read_string(text, i, line, line_start, source_name)
            tokens.append(Token(STRING, value, line, col(i)))
            continue

        # Numbers --------------------------------------------------------
        match = _NUMBER_RE.match(text, i)
        if match:
            raw = match.group(0)
            value = float(raw) if ("." in raw or "e" in raw or "E" in raw) else int(raw)
            tokens.append(Token(NUMBER, value, line, col(i)))
            i = match.end()
            continue

        # Identifiers and variables --------------------------------------
        match = _IDENT_RE.match(text, i)
        if match:
            tokens.append(Token(IDENT, match.group(0), line, col(i)))
            i = match.end()
            continue
        match = _VAR_RE.match(text, i)
        if match:
            tokens.append(Token(VAR, match.group(0), line, col(i)))
            i = match.end()
            continue

        # Operators and punctuation --------------------------------------
        for op in _OPERATORS:
            if text.startswith(op, i):
                tokens.append(Token(PUNCT, op, line, col(i)))
                i += len(op)
                break
        else:
            raise ParseError(
                "unexpected character %r" % ch, line, col(i), source_name
            )

    tokens.append(Token(EOF, None, line, col(i)))
    return tokens


def _read_string(text, i, line, line_start, source_name):
    """Read a quoted string starting at ``text[i]``; return ``(value, next_i)``."""
    quote = text[i]
    i += 1
    out = []
    n = len(text)
    while i < n:
        ch = text[i]
        if ch == quote:
            return "".join(out), i + 1
        if ch == "\n":
            break
        if ch == "\\":
            if i + 1 >= n:
                break
            nxt = text[i + 1]
            if nxt == "u":
                hexdigits = text[i + 2 : i + 6]
                if len(hexdigits) < 4 or not all(
                    c in "0123456789abcdefABCDEF" for c in hexdigits
                ):
                    raise ParseError(
                        "invalid \\u escape in string",
                        line,
                        i - line_start + 1,
                        source_name,
                    )
                out.append(chr(int(hexdigits, 16)))
                i += 6
                continue
            if nxt not in _ESCAPES:
                raise ParseError(
                    "unknown escape sequence \\%s" % nxt,
                    line,
                    i - line_start + 1,
                    source_name,
                )
            out.append(_ESCAPES[nxt])
            i += 2
            continue
        out.append(ch)
        i += 1
    raise ParseError("unterminated string literal", line, i - line_start + 1, source_name)
