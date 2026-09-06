# datalog

A small, dependency-free Datalog engine in Python: recursion, stratified
negation, arithmetic, and aggregates, evaluated bottom-up with semi-naive
iteration — or, when a query is narrow enough to be worth it, with magic sets.
Any fact it derives, it can also explain.

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
$ datalog run program.dl --demand     # derive only what the queries need
$ datalog explain 'path(a, d)' program.dl    # why is this fact true?
$ datalog check program.dl            # parse and validate, don't query
$ datalog repl program.dl             # interactive session
```

`python -m datalog ...` is equivalent, and `-` reads a program from stdin.
Useful flags: `--stats` (timing and tuple counts), `--strata` (how predicates
were stratified), `--warn-undefined` (flag predicates used but never defined,
which is usually a typo), `--demand` (see below). With `--demand`, `--stats`
reports each query's own evaluation rather than one figure for the program.

In the REPL, `:help` lists the commands — `:list`, `:preds`, `:show p`,
`:why f(a)`, `:strata`, `:stats`, `:load`, `:reset`, `:quit`. Entries spanning several lines
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

engine.query('path(a, X)', demand=True)  # same answers, only the work they need
```

`load()` returns any `?- ...` queries found in the source rather than running
them, so you decide when to evaluate. Evaluation is lazy and cached: `query()`
and `relation()` call `run()` for you, and adding a rule invalidates the cache.

Everything raises a subclass of `DatalogError`: `ParseError` (with line and
column), `SafetyError`, `StratificationError`, `EvaluationError`.

## Demand-driven evaluation

Bottom-up evaluation computes everything the program can derive. That is the
right trade for a broad question and the wrong one for a narrow one: `?- path(a,
X)` over a large graph builds the entire transitive closure and then keeps one
node's worth of it.

`--demand`, or `query(..., demand=True)`, answers a query by the **magic-set
transformation** instead. The program is rewritten so that each predicate gets a
companion recording which calls the query actually demands, and each rule is
guarded by it:

```prolog
// path(X, Y) :- edge(X, Z), path(Z, Y).   asked as   ?- path(a, W).
// becomes, writing m_path for "path was called with its first argument bound":

m_path(a).                                    // the query is the seed
path(X, Y) :- m_path(X), edge(X, Z), path(Z, Y).
m_path(Z)  :- m_path(X), edge(X, Z).          // the demand that rule creates
```

The guards make each rule fire only for demanded calls, and the last rule
propagates demand exactly the way the original rule passes bindings sideways —
so the fixpoint walks forward from `a` instead of building every path in the
graph. Same answers, less work — `examples/metro.dl` is twelve transit lines that
never meet, so eleven twelfths of it is irrelevant to any one journey:

```console
$ datalog run examples/metro.dl --stats          # statistics only, from stderr
134 rules, 2 predicates, 924 tuples, 1 strata, 13 iterations in 3.4 ms

$ datalog run examples/metro.dl --stats --demand
?- reaches(blue0, Stop).
  138 rules, 5 predicates, 222 tuples, 1 strata, 25 iterations in 1.5 ms
?- reaches(blue0, mint4).
  138 rules, 5 predicates, 145 tuples, 1 strata, 14 iterations in 0.8 ms
```

It is a trade, not a free win. Demand is derived in the same fixpoint as the
answers, so the two leapfrog: roughly two rounds per step of recursion, where
evaluating everything takes one. Narrow queries over a big database come out
well ahead; broad ones over a small database pay for the extra joins and get
nothing back. Measure before reaching for it.

The rewrite never changes what a query means, which leaves the engine free to
decline it and evaluate the whole program instead. It declines when the query
binds nothing (there would be no demand to push down), when the rules it reaches
use aggregates (an under-demanded aggregate would return a wrong number rather
than fewer rows), and when the rewritten program cannot be stratified — demand
for a negated goal has to be computed before the goal is read, and for some
programs no ordering does both. `--stats` says which queries were rewritten;
from Python, `result.stats` is `None` when the query fell back.

Demand evaluation runs in its own scratch engine, so it never leaves partial
relations behind: `engine.relation('path')` still means the whole of `path`.

## Why is this true?

A fixpoint tells you *what* holds. It does not tell you *why*, and for the
problems Datalog is good at — a policy that grants one permission too many, an
analysis that reports one alias too many — the tuple is rarely the interesting
part. The argument behind it is.

`datalog explain`, or `engine.explain(...)`, reconstructs that argument as a
proof tree: the rule that derived the fact, the premises that rule needed, and
so on down to the base facts the whole thing rests on.

```console
$ datalog explain 'allowed(alice, deploy, prod)' examples/access.dl
allowed(alice, deploy, prod)   by  allowed(U, Action, Object) :- granted(U, Action, Object), not denied(U, Action, Object).
├─ granted(alice, deploy, prod)   by  granted(U, Action, Object) :- hasRole(U, R), grant(R, Action, Object).
│  ├─ hasRole(alice, admin)   by  hasRole(U, R) :- memberOf(U, R).
│  │  └─ memberOf(alice, admin)
│  └─ grant(admin, deploy, prod)
└─ not denied(alice, deploy, prod)   (no such fact)
```

A line with `by` is a derived fact, and shows the rule that derived it; a line
without one is a base fact, written down in the program. Body literals that are
not atoms carry the rule's bindings substituted in, so you read `20 >= 18`
rather than `A >= 18`, `4 = (3 + 1)` rather than `Y = X + 1`, and a negation
that held is shown as the absence it is.

`--facts` prints only the leaves — the part of the database the conclusion
actually rests on, which is usually the part you were going to go and change:

```console
$ datalog explain 'allowed(alice, read, repo)' examples/access.dl --facts
grant(engineer, read, repo).
inherits(admin, engineer).
memberOf(alice, admin).
```

From Python the tree is an object rather than text — `derivation.support()` is
that same list of base facts, `depth` is the number of rule applications,
`rules_used()` the rules involved, `walk()` every node, and `to_dict()` a
JSON-shaped view (which is what `--json` prints):

```python
derivation = engine.explain('allowed(alice, read, repo)')
if derivation is None:
    print('not derivable')          # nothing to explain
else:
    print(derivation)               # the tree above
    print(derivation.support())     # the base facts it rests on
```

### Why the search terminates

Working backwards through a recursive program is the part that needs care.
`path(a, b)` may be derivable from `path(b, a)` and vice versa, so a backward
search that is not careful will either loop forever or spend exponential time
backtracking out of loops it wandered into. Worse, it may return a tree that
proves `path(a, b)` from `path(a, b)` — which looks entirely convincing until
you check it.

The way out is something semi-naive evaluation already computes. Evaluation
proceeds in rounds, and a tuple first derived in round *g* can only have come
from tuples that existed before round *g*: lower strata are finished before a
stratum starts, and within a stratum each round reads only what earlier rounds
produced. So the round a tuple first appeared in is a **well-founded measure**
on facts. The proof search records it and then refuses any step that would use
a fact from round *g* or later. Every step strictly descends, so the search
terminates without a cycle check and without backtracking, and no tree it
returns can contain a fact beneath itself. Within a stratum that measure *is*
the number of rule applications, so the proof is a shortest one too.

A fact usually has more than one derivation, and which one a search meets first
otherwise depends on the iteration order of a set — that is, on the process's
hash seed. Since a debugging tool that prints something different every run is
not much of a debugging tool, `explain` picks a canonical derivation instead:
the first applicable rule, and within it the smallest premises in the engine's
total order. The same program and the same fact always print the same tree.

Recording that round costs an integer per tuple, which is only worth paying if
you ask. Tracking is therefore off until you call `explain()` — which
re-evaluates once to switch it on — or build an `Engine(track_derivations=True)`.

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

*Derivations.* `explain()` runs backwards over the finished database, in
`datalog/explain.py`, using the round each tuple was first derived in as the
measure that keeps the search finite (see above). Nothing is replayed and no
provenance is threaded through evaluation: a proof is reconstructed from the
rules and the final relations, which is why tracking costs one integer per
tuple rather than a graph of them.

*Magic sets.* `--demand` inserts a rewriting pass between checking and
evaluation, adorning each predicate with the binding patterns the query reaches
it under and guarding its rules with the demand they generate. Two departures
from the textbook version, both in `datalog/magic.py`: adornments name the magic
predicates but not the relations, so `path` still means `path` and answers can
be read straight out of it; and the pass may return nothing at all, in which
case the query is answered the ordinary way.

## Tests

```console
$ python -m unittest discover -s tests -t .
```

The suite needs no dependencies and finishes in well under a second. It also
runs the module doctests and checks that every Datalog block in this README
still loads and evaluates, so the documentation cannot drift from the code.

Beyond unit coverage, three differential tests do the
heavy lifting on correctness: over random graphs, the engine's transitive
closure is compared against an independent BFS; the whole semi-naive fixpoint is
compared against a deliberately dumb naive evaluator that re-fires every rule
over the entire database until nothing changes; and every demand-driven answer
is compared against the same query answered by evaluating everything. The first
two guard the delta bookkeeping, which is the easiest thing in an engine like
this to get subtly wrong, by checking it against versions too simple to be
wrong. The third guards the magic-set rewrite the same way — and asserts that it
actually fired, since a transformation that always declines would agree with
itself perfectly.

Derivations get a fourth, of a different shape: a proof can be *checked*. A
verifier that shares no code with the search confirms that every leaf is a base
fact, that every step is a real instance of a real rule whose body holds in the
database, and — the point of the exercise — that no fact appears anywhere
beneath itself. Every fact derived by every bundled example, and by a run of
random cyclic graphs, is explained and then checked that way.

## Limitations

No function symbols or lists, no disjunction in rule bodies, and no persistence.
Predicates are identified by name *and* arity, and a single name may not be used
at two arities. Queries are answered bottom-up; `--demand` narrows that to what
the query needs (see above) but there is no top-down evaluation as such, and the
rewrite declines on programs whose relevant rules use aggregates.

`explain` answers why a fact *is* derivable. Why one is *not* is a genuinely
harder question — the honest answer is a description of every way it could have
been derived and where each one runs out — and the engine does not attempt it.
It explains one derivation, not all of them, and it explains facts rather than
query answers, so a query is a two-step affair: ask, then explain an answer.

## Examples

`examples/` holds five runnable programs: `ancestors.dl` (transitive closure,
negation, counting), `graph.dl` (reachability, cycles, shortest paths with
arithmetic, degrees), `access.dl` (role inheritance with deny-overrides-grant),
`pointsto.dl` (Andersen-style points-to analysis — the whole fixpoint algorithm
in four rules), and `metro.dl` (a deliberately disconnected network, to run
with and without `--demand`).

## License

MIT.
