# datalog

A small, dependency-free Datalog engine in Python: recursion, stratified
negation, arithmetic, and aggregates, evaluated bottom-up with semi-naive
iteration.

Datalog is the sweet spot between SQL and Prolog. It is declarative and always
terminates (no function symbols, so the set of derivable facts is finite), but
unlike SQL it does recursion natively. That combination makes it a very good fit
for reachability questions, access-control policies, and program analysis —
problems where the interesting part is the fixpoint, and you would rather not
hand-write the worklist loop.

```prolog
edge(a, b).  edge(b, c).  edge(c, d).

path(X, Y) :- edge(X, Y).
path(X, Y) :- edge(X, Z), path(Z, Y).

?- path(a, Where).
```

```console
$ datalog run graph.dl
?- path(a, Where).
  Where
  -----
  b
  c
  d
  3 answers.
```

Requires Python 3.9+. No third-party dependencies, at runtime or for the tests.

## Install

```console
$ pip install -e .
```

Or just vendor the `datalog/` package — it is pure standard library, and
`python -m datalog` works from a checkout with no install at all.

## The language

### Facts and rules

A **fact** is a ground atom. A **rule** derives new facts from existing ones;
read `:-` as "if" and `,` as "and".

```prolog
parent(alice, bob).                          // a fact
ancestor(X, Y) :- parent(X, Y).              // a rule
ancestor(X, Y) :- parent(X, Z), ancestor(Z, Y).
```

Names starting with a lowercase letter are predicates or symbol constants;
names starting with an uppercase letter or `_` are variables. A bare `_` is
anonymous, and every occurrence of it is a fresh variable.

Constants are symbols (`alice`), strings (`"alice"` or `'a b'`), integers, and
floats. A symbol and the string with the same characters are the same value, so
`alice` and `"alice"` are interchangeable — quotes are only needed for text that
is not a valid identifier.

Comments are `//` or `#` to end of line, or `/* ... */`.

### Queries

```prolog
?- ancestor(alice, Who).
?- ancestor(alice, Who), Who != bob.
?- ancestor(alice, dave).           // ground: answers yes or no
```

### Negation

`not p(...)` (or `!p(...)`) succeeds when no matching fact exists. This is
negation as failure over a *completed* relation, which is why the engine
stratifies (see below).

```prolog
root(X) :- parent(X, _), not parent(_, X).
```

Every variable under a negation must also appear in a positive literal of the
same rule. `_` is exempt, since `not r(X, _)` just means "no `r` fact starts
with X".

### Comparisons and arithmetic

`=`, `!=`, `<`, `<=`, `>`, `>=` compare values; `+`, `-`, `*`, `/`, `%` compute
them. `X = expr` binds `X` when it is free and tests equality when it is bound.

```prolog
adult(P) :- age(P, A), A >= 18.
next(X, Y) :- num(X), Y = X + 1.
```

Two details worth knowing:

* `/` returns an integer when the division is exact and a float otherwise, so
  `6 / 3` is `2` and `7 / 2` is `3.5`.
* Ordering comparisons use a **total order** in which every number sorts before
  every string. Mixed-type comparisons therefore give a definite answer instead
  of raising, and any relation can be sorted.

`+` also concatenates two strings.

### Aggregates

```text
Var = count { body }
Var = sum  expr { body }
Var = min  expr { body }
Var = max  expr { body }
Var = avg  expr { body }
```

Variables that the aggregate shares with the enclosing rule are the implicit
`GROUP BY` keys and must already be bound. Variables that occur only inside the
braces are local, and the aggregate ranges over the distinct combinations of
them.

```prolog
descendants(P, N) :- person(P), N = count { ancestor(P, _) }.
payroll(D, Total)  :- dept(D), Total = sum S { employee(E, D), salary(E, S) }.
```

Because `_` is an ordinary fresh variable, it counts as part of the thing being
counted: `count { r(K, U, _) }` counts distinct `(U, _)` pairs, not distinct `U`
values. To count distinct `U`, project first with a helper predicate.

`count` and `sum` over an empty group yield `0`. `min`, `max` and `avg` have no
answer for an empty group, so the enclosing rule simply does not fire for that
key. `min` and `max` use the same total order as `<`, so they work on strings;
`sum` and `avg` require numbers.

## Command line

```console
$ datalog run program.dl              # evaluate and answer the file's queries
$ datalog run program.dl -q 'path(a, X)'
$ datalog run program.dl --show path  # dump a whole relation
$ datalog run program.dl --json       # machine-readable output
$ datalog check program.dl            # parse and validate, don't query
$ datalog repl program.dl             # interactive session
```

`python -m datalog ...` is equivalent, and `-` reads a program from stdin.
Useful flags: `--stats` (timing and tuple counts), `--strata` (how predicates
were stratified), `--warn-undefined` (flag predicates used but never defined,
which is usually a typo).

In the REPL, `:help` lists the commands — `:list`, `:preds`, `:show p`,
`:strata`, `:stats`, `:load`, `:reset`, `:quit`. Entries spanning several lines
are read until a line ends with `.`. A clause that fails to load is rolled back,
so a mistake never corrupts the session.

## Python API

```python
from datalog import Engine

engine = Engine()
engine.load('''
    edge(a, b).  edge(b, c).
    path(X, Y) :- edge(X, Y).
    path(X, Y) :- edge(X, Z), path(Z, Y).
''')

for row in engine.query('path(a, X)'):
    print(row['X'])                      # -> b, c

engine.relation('path').tuples           # {('a','b'), ('b','c'), ('a','c')}
bool(engine.query('path(a, c)'))         # True — ground queries are yes/no
engine.stats                             # iterations, tuples, seconds, ...
```

`load()` returns any `?- ...` queries found in the source rather than running
them, so you decide when to evaluate. Evaluation is lazy and cached: `query()`
and `relation()` call `run()` for you, and adding a rule invalidates the cache.

Everything raises a subclass of `DatalogError`: `ParseError` (with line and
column), `SafetyError`, `StratificationError`, `EvaluationError`.

## How it works

**Parse → check → stratify → evaluate.**

*Safety.* A rule is safe when every variable it binds ranges over finitely many
values. Head variables must come from a positive atom, an assignment, or an
aggregate; negations and comparisons need their inputs bound. Rather than
demand a runnable literal order, the compiler **reorders each body**:
repeatedly emit the first remaining literal whose inputs are already bound. So
`p(X, Y) :- X < Y, q(X), r(Y).` is accepted and runs as `q(X), r(Y), X < Y`.
If nothing can be scheduled, the rule is genuinely unsafe and the error names
the offending variables.

*Stratification.* Negation only means something if the negated relation is
already complete. The engine builds a predicate dependency graph, finds its
strongly connected components with an iterative Tarjan (so a 4000-deep rule
chain does not blow the stack), and numbers the components so that a predicate
reached through negation or an aggregate always lands in a strictly lower
stratum. Recursion through negation makes that impossible — `p(X) :- q(X), not
p(X).` has no stratified model — and is rejected with the cycle spelled out.

*Semi-naive evaluation.* Strata are evaluated in order. Within a stratum, the
first round fires every rule; each later round re-fires a rule only against the
tuples derived in the previous round, since any genuinely new derivation must
use at least one of them. Relations keep lazily built, version-stamped indexes
on whichever argument positions are bound, so joins are hash lookups rather
than scans.

*Termination.* Pure Datalog always terminates, but arithmetic can invent new
constants forever (`p(Y) :- p(X), Y = X + 1.`). The engine caps iterations and
total tuples and raises `EvaluationError` with an explanation instead of
hanging. Both caps are constructor arguments.

## Tests

```console
$ python -m unittest discover -s tests -t .
```

The suite needs no dependencies and finishes in well under a second. It also
runs the module doctests and checks that every Datalog block in this README
still loads and evaluates, so the documentation cannot drift from the code.

Beyond unit coverage, two differential tests do the
heavy lifting on correctness: over random graphs, the engine's transitive
closure is compared against an independent BFS, and — more importantly — the
whole semi-naive fixpoint is compared against a deliberately dumb naive
evaluator that re-fires every rule over the entire database until nothing
changes. The delta bookkeeping is the easiest thing in an engine like this to
get subtly wrong, so it is checked against a version too simple to be wrong.

## Limitations

No function symbols or lists, no disjunction in rule bodies, no top-down/magic-set
evaluation (queries are answered by evaluating the whole program bottom-up,
which is the wrong trade for a large database and a very selective query), and
no persistence. Predicates are identified by name *and* arity, and a single name
may not be used at two arities.

## Examples

`examples/` holds four runnable programs: `ancestors.dl` (transitive closure,
negation, counting), `graph.dl` (reachability, cycles, shortest paths with
arithmetic, degrees), `access.dl` (role inheritance with deny-overrides-grant),
and `pointsto.dl` (Andersen-style points-to analysis — the whole fixpoint
algorithm in four rules).

## License

MIT.
