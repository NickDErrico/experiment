"""Command-line interface: ``datalog run``, ``datalog check`` and ``datalog repl``."""

from __future__ import annotations

import argparse
import json
import os
import sys

from . import __version__
from .engine import Engine
from .errors import DatalogError
from .syntax import format_value

_BANNER = "datalog %s - type :help for commands, :quit to exit" % __version__

_HELP = """\
Commands
  :help              show this message
  :quit  :q          leave the repl
  :load FILE         load rules from a file
  :list              show every rule currently loaded
  :preds             list known predicates and their sizes
  :show PRED[/N]     print all tuples of a relation
  :strata            show how predicates are stratified
  :stats             show statistics for the last evaluation
  :reset             forget every rule and start over

Anything else is Datalog. Clauses end with '.', queries start with '?-':
  parent(alice, bob).
  ancestor(X, Y) :- parent(X, Y).
  ?- ancestor(alice, X).
An entry spanning several lines is read until it ends with '.'."""


# --------------------------------------------------------------------------
# Shared helpers
# --------------------------------------------------------------------------


def _read(path):
    if path == "-":
        return sys.stdin.read(), "<stdin>"
    with open(path, "r", encoding="utf-8") as handle:
        return handle.read(), path


def format_result(result, indent="  "):
    """Render a :class:`~datalog.engine.QueryResult` as aligned text."""
    if result.is_ground:
        return indent + ("yes." if result.rows else "no.")
    if not result.rows:
        return indent + "no answers."

    columns = result.variables
    cells = [[format_value(value) for value in row] for row in result.rows]
    widths = [len(name) for name in columns]
    for row in cells:
        for position, text in enumerate(row):
            widths[position] = max(widths[position], len(text))

    lines = [
        indent + "  ".join(name.ljust(widths[i]) for i, name in enumerate(columns)).rstrip(),
        indent + "  ".join("-" * widths[i] for i in range(len(columns))),
    ]
    for row in cells:
        lines.append(
            indent + "  ".join(text.ljust(widths[i]) for i, text in enumerate(row)).rstrip()
        )
    plural = "" if len(cells) == 1 else "s"
    lines.append(indent + "%d answer%s." % (len(cells), plural))
    return "\n".join(lines)


def format_relation(relation, indent="  "):
    if not len(relation):
        return indent + "(empty)"
    lines = []
    for tup in relation.sorted_tuples():
        if relation.arity:
            lines.append(
                indent
                + "%s(%s)." % (relation.name, ", ".join(format_value(v) for v in tup))
            )
        else:
            lines.append(indent + "%s." % relation.name)
    return "\n".join(lines)


def _parse_predicate(spec):
    """Split ``name`` or ``name/arity`` into ``(name, arity_or_None)``."""
    if "/" in spec:
        name, _, arity = spec.rpartition("/")
        try:
            return name, int(arity)
        except ValueError:
            raise DatalogError("bad predicate spec %r; use name or name/arity" % spec)
    return spec, None


def _resolve_relations(engine, specs):
    relations = []
    for spec in specs:
        name, arity = _parse_predicate(spec)
        relations.append(engine.relation(name, arity))
    return relations


# --------------------------------------------------------------------------
# run
# --------------------------------------------------------------------------


def command_run(args):
    engine = Engine()
    queries = []
    for path in args.files:
        text, name = _read(path)
        queries.extend(engine.load(text, name))
    for text in args.query or []:
        queries.append(_single_query(text))

    if not args.demand:
        # In demand mode each query drives its own evaluation, so there is
        # nothing to compute up front.
        engine.run()

    if args.warn_undefined:
        for name, arity in engine.undefined_predicates():
            print(
                "warning: %s/%d is used but never defined; it is empty"
                % (name, arity),
                file=sys.stderr,
            )

    results = [(query, engine.query(query, demand=args.demand)) for query in queries]

    if args.show_all:
        shown = [
            engine.relation(name, arity)
            for name, arity in engine.predicates()
        ]
    else:
        shown = _resolve_relations(engine, args.show or [])

    if args.json:
        payload = {
            "queries": [_query_payload(q, r) for q, r in results],
            "relations": {
                "%s/%d" % (rel.name, rel.arity): [list(t) for t in rel.sorted_tuples()]
                for rel in shown
            },
            "stats": engine.stats,
        }
        json.dump(payload, sys.stdout, indent=2, sort_keys=False)
        sys.stdout.write("\n")
    else:
        for relation in shown:
            print("%% %s/%d (%d tuples)" % (relation.name, relation.arity, len(relation)))
            print(format_relation(relation))
            print()
        for query, result in results:
            print(query)
            print(format_result(result))
            print()

    if args.strata:
        _print_strata(engine, sys.stderr)
    if args.stats:
        if args.demand:
            for query, result in results:
                _print_query_stats(query, result, engine, sys.stderr)
        else:
            _print_stats(engine.stats, sys.stderr)
    return 0


def _query_payload(query, result):
    payload = {
        "query": str(query),
        "variables": result.variables,
        "rows": [list(row) for row in result.rows],
    }
    if result.stats is not None:
        payload["stats"] = result.stats
    return payload


def _print_query_stats(query, result, engine, stream):
    """Report what answering one query cost, in demand mode."""
    print(query, file=stream)
    if result.stats is None:
        print(
            "  (not rewritten; answered by evaluating the whole program)",
            file=stream,
        )
        _print_stats(engine.stats, stream, indent="  ")
    else:
        _print_stats(result.stats, stream, indent="  ")


def _single_query(text):
    from .parser import parse

    stripped = text.strip()
    if not stripped.startswith("?-"):
        stripped = "?- " + stripped
    if not stripped.endswith("."):
        stripped += "."
    program = parse(stripped, "<argument>")
    if len(program.queries) != 1 or program.rules:
        raise DatalogError("--query expects exactly one goal, got %r" % text)
    return program.queries[0]


def _print_stats(stats, stream, indent=""):
    print(
        indent
        + "%d rules, %d predicates, %d tuples, %d strata, %d iterations in %.1f ms"
        % (
            stats.get("rules", 0),
            stats.get("predicates", 0),
            stats.get("tuples", 0),
            stats.get("strata", 0),
            stats.get("iterations", 0),
            1000 * stats.get("seconds", 0.0),
        ),
        file=stream,
    )


def _print_strata(engine, stream):
    for level, predicates in enumerate(engine.strata):
        names = ", ".join("%s/%d" % sig for sig in sorted(predicates))
        print("stratum %d: %s" % (level, names), file=stream)


# --------------------------------------------------------------------------
# check
# --------------------------------------------------------------------------


def command_check(args):
    engine = Engine()
    for path in args.files:
        text, name = _read(path)
        engine.load(text, name)
    engine.run()
    undefined = engine.undefined_predicates()
    for name, arity in undefined:
        print("warning: %s/%d is used but never defined" % (name, arity), file=sys.stderr)
    print(
        "ok: %d rules, %d strata" % (len(engine.rules), len(engine.strata)),
        file=sys.stderr,
    )
    return 0


# --------------------------------------------------------------------------
# repl
# --------------------------------------------------------------------------


def command_repl(args):
    engine = Engine()
    for path in args.files:
        text, name = _read(path)
        for query in engine.load(text, name):
            print(query)
            print(format_result(engine.query(query)))
    if args.files:
        engine.run()
        print("loaded %d rules from %s" % (len(engine.rules), ", ".join(args.files)))

    _install_readline()
    print(_BANNER)

    buffer = ""
    while True:
        prompt = "?- " if not buffer else "   "
        try:
            line = input(prompt)
        except EOFError:
            print()
            return 0
        except KeyboardInterrupt:
            print("^C")
            buffer = ""
            continue

        stripped = line.strip()
        if not buffer and stripped.startswith(":"):
            if _repl_command(engine, stripped):
                return 0
            continue
        if not buffer and not stripped:
            continue

        buffer = (buffer + "\n" + line) if buffer else line
        if not buffer.rstrip().endswith("."):
            continue

        text, buffer = buffer, ""
        try:
            _repl_input(engine, text)
        except DatalogError as exc:
            print("error: %s" % exc, file=sys.stderr)


def _repl_input(engine, text):
    """Evaluate one complete REPL entry: clauses are added, queries are run."""
    before = len(engine.rules)
    try:
        queries = engine.load(text, "<repl>")
    except DatalogError:
        # A parse or safety error may still have accepted earlier clauses in
        # the same entry; drop them so the session state stays predictable.
        engine.truncate_rules(before)
        raise
    added = len(engine.rules) - before
    try:
        engine.run()
    except DatalogError:
        # Roll the offending clauses back so the session stays usable.
        engine.truncate_rules(before)
        raise
    for query in queries:
        print(format_result(engine.query(query)))
    if added and not queries:
        print("  ok (%d clause%s)" % (added, "" if added == 1 else "s"))


def _repl_command(engine, line):
    """Handle a ``:command``.  Returns True when the REPL should exit."""
    parts = line.split()
    name = parts[0]
    argument = parts[1] if len(parts) > 1 else None

    if name in (":quit", ":q", ":exit"):
        return True
    if name in (":help", ":h", ":?"):
        print(_HELP)
    elif name == ":list":
        if not engine.rules:
            print("  (no rules loaded)")
        for rule in engine.rules:
            print("  %s" % rule)
    elif name == ":preds":
        try:
            engine.run()
        except DatalogError as exc:
            print("error: %s" % exc, file=sys.stderr)
            return False
        for signature in engine.predicates():
            relation = engine.relations[signature]
            print("  %s/%d  %d tuples" % (signature[0], signature[1], len(relation)))
    elif name == ":show":
        if not argument:
            print("usage: :show PRED[/ARITY]", file=sys.stderr)
        else:
            try:
                predicate, arity = _parse_predicate(argument)
                print(format_relation(engine.relation(predicate, arity)))
            except DatalogError as exc:
                print("error: %s" % exc, file=sys.stderr)
    elif name == ":strata":
        try:
            engine.run()
            _print_strata(engine, sys.stdout)
        except DatalogError as exc:
            print("error: %s" % exc, file=sys.stderr)
    elif name == ":stats":
        try:
            engine.run()
            _print_stats(engine.stats, sys.stdout)
        except DatalogError as exc:
            print("error: %s" % exc, file=sys.stderr)
    elif name == ":load":
        if not argument:
            print("usage: :load FILE", file=sys.stderr)
        else:
            try:
                text, source = _read(argument)
                for query in engine.load(text, source):
                    print(query)
                    print(format_result(engine.query(query)))
                engine.run()
                print("  loaded %s (%d rules total)" % (argument, len(engine.rules)))
            except (OSError, DatalogError) as exc:
                print("error: %s" % exc, file=sys.stderr)
    elif name == ":reset":
        engine.reset()
        print("  cleared")
    else:
        print("unknown command %s (try :help)" % name, file=sys.stderr)
    return False


def _install_readline():
    """Enable history and line editing for interactive sessions.

    Skipped when input is piped, so scripted use never touches the user's
    history file.
    """
    try:
        if not sys.stdin.isatty():
            return
    except (AttributeError, ValueError):
        return
    try:
        import readline
    except ImportError:  # pragma: no cover - Windows without pyreadline
        return
    history = os.path.expanduser("~/.datalog_history")
    try:
        readline.read_history_file(history)
    except (OSError, ValueError):
        pass
    try:
        readline.set_history_length(1000)
        import atexit

        atexit.register(_save_history, readline, history)
    except Exception:  # pragma: no cover - best effort only
        pass


def _save_history(readline, path):  # pragma: no cover - runs at interpreter exit
    try:
        readline.write_history_file(path)
    except OSError:
        pass


# --------------------------------------------------------------------------
# Argument parsing
# --------------------------------------------------------------------------


def build_parser():
    parser = argparse.ArgumentParser(
        prog="datalog",
        description="A small Datalog engine: recursion, stratified negation, "
        "aggregates, magic sets.",
    )
    parser.add_argument("--version", action="version", version="datalog " + __version__)
    subparsers = parser.add_subparsers(dest="command")

    run = subparsers.add_parser("run", help="evaluate a program and answer its queries")
    run.add_argument("files", nargs="+", help="Datalog source files ('-' for stdin)")
    run.add_argument(
        "-q", "--query", action="append", metavar="GOAL", help="extra goal to answer"
    )
    run.add_argument(
        "-s", "--show", action="append", metavar="PRED", help="print a relation"
    )
    run.add_argument("--show-all", action="store_true", help="print every relation")
    run.add_argument("--json", action="store_true", help="emit JSON instead of text")
    run.add_argument(
        "--demand",
        action="store_true",
        help="answer each query by magic sets: rewrite the program to derive "
        "only what the query needs",
    )
    run.add_argument("--stats", action="store_true", help="report evaluation statistics")
    run.add_argument("--strata", action="store_true", help="report the stratification")
    run.add_argument(
        "--warn-undefined",
        action="store_true",
        help="warn about predicates used but never defined",
    )
    run.set_defaults(handler=command_run)

    check = subparsers.add_parser("check", help="parse and validate without querying")
    check.add_argument("files", nargs="+", help="Datalog source files ('-' for stdin)")
    check.set_defaults(handler=command_check)

    repl = subparsers.add_parser("repl", help="start an interactive session")
    repl.add_argument("files", nargs="*", help="files to preload")
    repl.set_defaults(handler=command_repl)

    return parser


def main(argv=None):
    parser = build_parser()
    args = parser.parse_args(argv)
    if not getattr(args, "handler", None):
        parser.print_help()
        return 2
    try:
        return args.handler(args)
    except DatalogError as exc:
        print("error: %s" % exc, file=sys.stderr)
        return 1
    except OSError as exc:
        print("error: %s" % exc, file=sys.stderr)
        return 1
    except BrokenPipeError:  # pragma: no cover
        return 0


if __name__ == "__main__":  # pragma: no cover
    sys.exit(main())
