"""Incremental maintenance: keeping a fixpoint current as facts come and go.

Evaluation computes a fixpoint from nothing.  That is the right thing to do
once, and the wrong thing to do again every time a single fact changes: an
access-control policy is not reloaded from scratch because one person joined
one group, and a program analysis is not re-run from scratch because one line
was edited.

Adding facts is the easy half.  Datalog without negation is monotone, so an
insertion can only ever *add* consequences, and the semi-naive loop already
knows how to chase those: seed it with the new tuples and let it run.

Deletion is the hard half, and it is hard for one specific reason.  A derived
fact does not belong to the rule that happened to derive it first — it holds
because *some* derivation supports it, and a fact usually has many.  Retracting
``edge(a, b)`` does not retract ``path(a, c)`` unless every path from ``a`` to
``c`` went through that edge, and nothing in the database says whether one did.
The support is not stored; it was consumed during evaluation and thrown away.

**DRed** (delete and rederive) answers that question by splitting it in two,
because the cheap over-approximation and the expensive exact check have very
different costs:

1. *Overdelete.*  Assume the worst.  Every fact with a derivation that touched
   something deleted is provisionally deleted too, and that assumption
   propagates transitively.  This is a pure forward chase over deltas — the
   same machinery as insertion, run over the *old* database — and it is fast.
2. *Rederive.*  Now check.  For each provisionally deleted fact, ask whether it
   still follows from what survived.  A fact that does comes back.  Because a
   restored fact can support another, this is itself a fixpoint: restore in
   rounds until a round restores nothing.
3. *Insert.*  Chase the newly asserted facts, and everything the deletions made
   *newly* true, with ordinary semi-naive iteration.

The cost of step 1 being an over-approximation is that step 2 sometimes tears
down a fact only to rebuild it.  The alternative — storing a support count per
tuple — would make deletion exact, but taxes every insertion and every byte of
the database whether or not anything is ever retracted.  DRed keeps the tax on
the operation that asks for it.

Negation and aggregation are where an incremental algorithm usually goes wrong,
and stratification is what makes them tractable here.  Both cross strata
*strictly*: a negated or aggregated predicate always lives strictly below the
rule that reads it.  So if the strata are maintained in order, a stratum is
only ever maintained against lower strata that are already final, and the
awkward cases become ordinary:

* a deletion below can *add* facts above, because ``not q(x)`` starts holding;
* an insertion below can *remove* facts above, for the same reason in reverse;
* any change below can move an aggregate, so every fact the aggregating rule
  produced is over-deleted and re-derived against the new numbers.

Within a stratum there is no negation to worry about — stratification forbids
it — so the propagation there is purely monotone in both directions.

What is *not* incremental is a change to the rules.  Rules determine the
stratification, and a new stratification renumbers the very order this
algorithm walks.  :meth:`datalog.Engine.update` detects that case and falls
back to evaluating everything, which is always correct and is exactly what the
engine did before this module existed.
"""

from __future__ import annotations

import time
from collections import defaultdict

from .errors import EvaluationError
from .safety import order_body
from .syntax import (
    Aggregate,
    Atom,
    Const,
    Literal,
    body_predicates,
    sort_key,
)

_MISSING = object()


# --------------------------------------------------------------------------
# The result of an update
# --------------------------------------------------------------------------


class Delta:
    """What an update did to the database: the facts it added and removed.

    Both are keyed by predicate signature, ``(name, arity)``, and hold sets of
    ground tuples.  Only predicates that actually changed appear.

    >>> from datalog import Engine
    >>> engine = Engine()
    >>> _ = engine.load('edge(a, b). edge(b, c).'
    ...                 'path(X, Y) :- edge(X, Y).'
    ...                 'path(X, Y) :- edge(X, Z), path(Z, Y).')
    >>> print(engine.assert_fact('edge(c, d)'))
    + edge(c, d)
    + path(a, d)
    + path(b, d)
    + path(c, d)
    >>> print(engine.retract_fact('edge(b, c)'))
    - edge(b, c)
    - path(a, c)
    - path(a, d)
    - path(b, c)
    - path(b, d)
    """

    __slots__ = ("added", "removed", "stats")

    def __init__(self, added=None, removed=None, stats=None):
        self.added = {sig: set(tuples) for sig, tuples in (added or {}).items() if tuples}
        self.removed = {
            sig: set(tuples) for sig, tuples in (removed or {}).items() if tuples
        }
        #: Statistics for the maintenance that produced this delta.  ``mode`` is
        #: ``"incremental"`` or ``"recompute"``; see :meth:`datalog.Engine.update`.
        self.stats = stats or {}

    def __bool__(self):
        return bool(self.added or self.removed)

    def __len__(self):
        """The total number of facts that changed."""
        return sum(len(t) for t in self.added.values()) + sum(
            len(t) for t in self.removed.values()
        )

    @property
    def predicates(self):
        """Signatures touched by this update, sorted."""
        return sorted(set(self.added) | set(self.removed))

    def added_facts(self, name=None):
        """Added facts as :class:`~datalog.syntax.Atom` objects, in a stable order."""
        return _atoms(self.added, name)

    def removed_facts(self, name=None):
        """Removed facts as :class:`~datalog.syntax.Atom` objects, in a stable order."""
        return _atoms(self.removed, name)

    def to_dict(self):
        """A JSON-shaped view of the change."""
        return {
            "added": [str(atom) for atom in self.added_facts()],
            "removed": [str(atom) for atom in self.removed_facts()],
            "stats": dict(self.stats),
        }

    def format(self, name=None):
        """The change as a diff: ``+`` for added facts, ``-`` for removed ones."""
        lines = ["- %s" % atom for atom in self.removed_facts(name)]
        lines += ["+ %s" % atom for atom in self.added_facts(name)]
        lines.sort(key=lambda line: (line[2:], line[0]))
        return "\n".join(lines)

    def __str__(self):
        return self.format()

    def __repr__(self):
        return "<Delta +%d -%d>" % (
            sum(len(t) for t in self.added.values()),
            sum(len(t) for t in self.removed.values()),
        )


def _atoms(changes, name=None):
    """Ground atoms for a ``{signature: tuples}`` mapping, in the total order."""
    out = []
    for signature in sorted(changes):
        if name is not None and signature[0] != name:
            continue
        predicate = signature[0]
        for tup in sorted(changes[signature], key=lambda t: tuple(sort_key(v) for v in t)):
            out.append(Atom(predicate, tuple(Const(value) for value in tup)))
    return out


# --------------------------------------------------------------------------
# Maintenance
# --------------------------------------------------------------------------


def diff(before, after, stats=None):
    """The :class:`Delta` between two ``{signature: tuple-set}`` snapshots.

    Used when a change is too structural to maintain incrementally and the
    program is simply re-evaluated: the answer is the same, only the route to
    it is different.
    """
    added = {}
    removed = {}
    for signature in set(before) | set(after):
        old = before.get(signature, frozenset())
        new = after.get(signature, frozenset())
        if new - old:
            added[signature] = new - old
        if old - new:
            removed[signature] = old - new
    return Delta(added, removed, stats)


def maintain(engine, inserted, deleted):
    """Bring ``engine``'s relations up to date after a change to its facts.

    ``inserted`` and ``deleted`` map signatures to sets of ground tuples that
    were asserted and retracted.  The engine's rule list must already reflect
    the change; its relations must still hold the previous fixpoint.  Returns a
    :class:`Delta` describing every derived fact that appeared or disappeared.
    """
    return _Maintainer(engine, inserted, deleted).run()


class _Maintainer:
    """One incremental update, walking the strata in order."""

    def __init__(self, engine, inserted, deleted):
        self.engine = engine
        self.inserted = {sig: set(t) for sig, t in inserted.items() if t}
        self.deleted = {sig: set(t) for sig, t in deleted.items() if t}
        #: Net change so far, by signature.  Strata below the one being
        #: maintained are final, so these are what higher strata react to.
        self.added = {}
        self.removed = {}
        #: ``{signature: (added, removed)}`` for the relations maintained so
        #: far, from which their pre-update state can be reconstructed on demand.
        self._changes = {}
        self._old = {}
        self.iterations = 0
        self.rederived = 0

    # -- driving ----------------------------------------------------------

    def run(self):
        engine = self.engine
        started = time.perf_counter()

        by_stratum = defaultdict(list)
        for rule in engine.rules:
            by_stratum[engine.stratum_of[rule.head.signature]].append(rule)

        for level in range(len(engine.strata)):
            self._stratum(level, by_stratum.get(level, []), engine.strata[level])

        return Delta(
            self.added,
            self.removed,
            {
                "mode": "incremental",
                "iterations": self.iterations,
                "rederived": self.rederived,
                "tuples": sum(len(rel) for rel in engine.relations.values()),
                "seconds": time.perf_counter() - started,
            },
        )

    def _stratum(self, level, rules, predicates):
        """Maintain one stratum against changes already applied below it."""
        # A predicate of this stratum that was directly asserted or retracted
        # changes even if no rule of the stratum reads anything that moved --
        # including when the retraction was of its last remaining fact, leaving
        # the stratum with no rules for it at all.
        touched = {
            signature
            for signature in predicates
            if self.inserted.get(signature) or self.deleted.get(signature)
        }
        triggers = self._triggers(rules, level)
        if not triggers and not touched:
            return  # nothing this stratum reads has changed

        candidates = self._overdelete(rules, predicates, triggers)
        self._apply_deletions(candidates)

        # Everything provisionally deleted, less whatever comes back.  Tracking
        # the change itself rather than diffing snapshots is what keeps an
        # update proportional to what it touches: a relation of a million tuples
        # is never copied to discover that three of them moved.
        pending = {signature: set(tuples) for signature, tuples in candidates.items()}
        self._rederive(pending, rules)
        committed = self._insert(rules, predicates, triggers)

        for signature in set(pending) | set(committed):
            gone = pending.get(signature, ())
            new = committed.get(signature, ())
            removed = {tup for tup in gone if tup not in new}
            added = {tup for tup in new if tup not in gone}
            if added:
                self.added[signature] = added
            if removed:
                self.removed[signature] = removed
            if added or removed:
                self._changes[signature] = (added, removed)

    # -- what changed underneath ------------------------------------------

    def _triggers(self, rules, level):
        """Per-rule descriptions of how each rule is affected by the update.

        A rule can be reached by a change in four ways, and they need different
        treatment, so they are worked out once here rather than at every use:

        ``positions``
            positive body literals below this stratum whose relation changed,
            which can be chased one delta at a time;
        ``negations``
            negated body literals whose relation changed — a gain there deletes,
            a loss there inserts;
        ``aggregate``
            the rule aggregates over something that changed, so its numbers may
            have moved and it has to be re-run whole.
        """
        engine = self.engine
        triggers = {}
        for index, rule in enumerate(rules):
            positions = []
            negations = []
            aggregate = False
            for position, literal in enumerate(rule.body):
                if isinstance(literal, Literal):
                    signature = literal.atom.signature
                    if engine.stratum_of.get(signature, level) >= level:
                        continue  # same stratum: handled by the inner fixpoint
                    if literal.negated:
                        if self.added.get(signature) or self.removed.get(signature):
                            negations.append(position)
                    elif self.added.get(signature) or self.removed.get(signature):
                        positions.append(position)
                elif isinstance(literal, Aggregate):
                    inner, negative = body_predicates((literal,))
                    if any(
                        self.added.get(sig) or self.removed.get(sig)
                        for sig in inner | negative
                    ):
                        aggregate = True
            if positions or negations or aggregate:
                triggers[index] = (positions, negations, aggregate)
        return triggers

    # -- step 1: overdelete ------------------------------------------------

    def _overdelete(self, rules, predicates, triggers):
        """Every tuple of this stratum whose support the update may have cut.

        Chased over the database as it stood *before* the update, because a
        derivation that is going away is by definition one that only the old
        database has.  Lower strata have already been maintained by the time we
        get here, so their old state is reconstructed from the changes recorded
        for them; this stratum has not been touched yet, so it still *is* its
        own old state.
        """
        engine = self.engine
        candidates = defaultdict(set)

        saved = engine.relations
        engine.relations = dict(saved)
        for signature in _body_signatures(rules):
            if signature in self._changes:
                engine.relations[signature] = self._old_relation(signature, saved)
        try:
            produced = defaultdict(set)

            # Retracted facts are the seed: a fact rule that is gone can no
            # longer support its head.
            for signature, tuples in self.deleted.items():
                if signature in predicates:
                    produced[signature] |= tuples

            for index, rule in enumerate(rules):
                trigger = triggers.get(index)
                if trigger is None:
                    continue
                positions, negations, aggregate = trigger
                bucket = produced[rule.head.signature]
                if aggregate:
                    # The aggregate may have moved; every fact this rule made
                    # is suspect.  Rederivation re-runs it against the new
                    # numbers and keeps whatever still holds.
                    self._derive(rule, rule.body, None, None, bucket)
                    continue
                for position in positions:
                    signature = rule.body[position].atom.signature
                    lost = self.removed.get(signature)
                    if lost:
                        self._derive(
                            rule, rule.body, position, self._wrap(signature, lost), bucket
                        )
                for position in negations:
                    # A negated goal that gained tuples stopped holding.  Read
                    # the literal positively against just those tuples to find
                    # the derivations it used to permit.
                    signature = rule.body[position].atom.signature
                    gained = self.added.get(signature)
                    if gained:
                        body = _positive(rule.body, position)
                        self._derive(
                            rule, body, position, self._wrap(signature, gained), bucket
                        )

            frontier = self._absorb(produced, candidates)

            # Now propagate within the stratum: a tuple whose support is gone
            # cannot support anything else either.
            recursive = _recursive_positions(rules, predicates)
            while frontier:
                self._count_iteration()
                produced = defaultdict(set)
                for rule, positions in recursive:
                    for position in positions:
                        signature = rule.body[position].atom.signature
                        lost = frontier.get(signature)
                        if lost:
                            self._derive(
                                rule,
                                rule.body,
                                position,
                                self._wrap(signature, lost),
                                produced[rule.head.signature],
                            )
                frontier = self._absorb(produced, candidates)
        finally:
            engine.relations = saved

        return {sig: tuples for sig, tuples in candidates.items() if tuples}

    def _absorb(self, produced, candidates):
        """Fold newly marked tuples into ``candidates``; return the genuinely new."""
        frontier = {}
        for signature, tuples in produced.items():
            if not tuples:
                continue
            # Only tuples that are actually in the database can be deleted from
            # it; firing over the old database can otherwise re-propose a tuple
            # some other rule already marked.
            known = self.engine._relation(signature).tuples
            fresh = {t for t in tuples if t in known} - candidates[signature]
            if fresh:
                candidates[signature] |= fresh
                frontier[signature] = fresh
        return frontier

    def _apply_deletions(self, candidates):
        for signature, tuples in candidates.items():
            relation = self.engine._relation(signature)
            relation.remove(tuples)
            if relation.rounds:
                for tup in tuples:
                    relation.rounds.pop(tup, None)

    # -- step 2: rederive --------------------------------------------------

    def _rederive(self, pending, rules):
        """Put back every over-deleted tuple that still follows from what is left.

        A restored tuple can be the missing premise of another, so this runs to
        a fixpoint.  Restorations are applied in batches, one round at a time,
        so a fact is never restored using something restored in the same round.
        That keeps every fact's generation strictly greater than the generations
        of the facts supporting it, which is the property :mod:`datalog.explain`
        relies on to walk a proof backwards without looping.
        """
        if not pending:
            return
        engine = self.engine
        by_head = defaultdict(list)
        for rule in rules:
            by_head[rule.head.signature].append(rule)

        while True:
            self._count_iteration()
            restored = {}
            for signature, tuples in pending.items():
                back = {
                    tup
                    for tup in tuples
                    if self._derivable(by_head.get(signature, ()), tup)
                }
                if back:
                    restored[signature] = back
            if not restored:
                return
            engine._generation += 1
            for signature, tuples in restored.items():
                relation = engine._relation(signature)
                relation.update(tuples)
                if engine.track_derivations:
                    for tup in tuples:
                        relation.rounds[tup] = engine._generation
                pending[signature] -= tuples
                self.rederived += len(tuples)

    def _derivable(self, rules, tup):
        """Is ``tup`` still derivable by one of ``rules`` from the current database?

        The head is bound to the tuple up front so the search only explores
        derivations of *this* fact.  That is sound because safety guarantees
        every head variable is bound before any literal that reads it — an
        aggregate included, since a head variable inside an aggregate body is
        necessarily one of its group keys.
        """
        for rule in rules:
            binding = {}
            for term, value in zip(rule.head.terms, tup):
                if isinstance(term, Const):
                    if term.value != value:
                        break
                else:
                    seen = binding.get(term.name, _MISSING)
                    if seen is _MISSING:
                        binding[term.name] = value
                    elif seen != value:
                        break
            else:
                for found in self._heads(rule, rule.body, None, None, binding):
                    if found == tup:
                        return True
        return False

    # -- step 3: insert ----------------------------------------------------

    def _insert(self, rules, predicates, triggers):
        """Chase everything the update made newly true, semi-naively."""
        engine = self.engine
        produced = defaultdict(set)

        for signature, tuples in self.inserted.items():
            if signature in predicates:
                produced[signature] |= tuples - engine._relation(signature).tuples

        for index, rule in enumerate(rules):
            trigger = triggers.get(index)
            if trigger is None:
                continue
            positions, negations, aggregate = trigger
            if aggregate:
                engine._fire(rule, produced, None, None)
                continue
            for position in positions:
                signature = rule.body[position].atom.signature
                gained = self.added.get(signature)
                if gained:
                    engine._fire(rule, produced, position, self._wrap(signature, gained))
            for position in negations:
                # A negated goal that lost tuples may have started holding.
                # Reading it positively against exactly what it lost narrows
                # the search to the bindings that could have changed -- but it
                # also stops checking the negation, and the goal may still be
                # blocked by a tuple that did not go away.  So these are
                # candidates, and each one is confirmed against the real rule.
                signature = rule.body[position].atom.signature
                lost = self.removed.get(signature)
                if not lost:
                    continue
                body = _positive(rule.body, position)
                known = engine._relation(rule.head.signature).tuples
                candidates = set(
                    self._heads(rule, body, position, self._wrap(signature, lost), {})
                )
                for tup in candidates - known:
                    if self._derivable((rule,), tup):
                        produced[rule.head.signature].add(tup)

        committed = defaultdict(set)
        delta = engine._commit(produced)
        if not delta:
            return committed

        recursive = _recursive_positions(rules, predicates)
        while any(relation.tuples for relation in delta.values()):
            for signature, relation in delta.items():
                committed[signature] |= relation.tuples
            self._count_iteration()
            produced = defaultdict(set)
            for rule, positions in recursive:
                for position in positions:
                    source = delta.get(rule.body[position].atom.signature)
                    if source is not None and source.tuples:
                        engine._fire(rule, produced, position, source)
            delta = engine._commit(produced)
        return committed

    # -- shared machinery --------------------------------------------------

    def _derive(self, rule, body, delta_position, delta_relation, bucket):
        """Collect every head tuple ``rule`` produces, whether or not it is known.

        ``Engine._fire`` filters out tuples the database already holds, which is
        what insertion wants and the opposite of what overdeletion wants.
        """
        bucket.update(self._heads(rule, body, delta_position, delta_relation, {}))

    def _heads(self, rule, body, delta_position, delta_relation, binding):
        terms = rule.head.terms
        if delta_position:
            # Always drive from the delta here: maintenance deltas are small by
            # construction, which is the whole point of doing it this way.  The
            # body may be a substituted one (a negation read positively), which
            # the rule cannot have cached, so reorder that one on the spot.
            if body is rule.body:
                body = rule.delta_body(delta_position)
            else:
                body = tuple(order_body(body, set(), first=delta_position)[0])
            delta_position = 0
        for solution in self.engine._solve(
            body, 0, binding, delta_position, delta_relation
        ):
            yield tuple(
                term.value if isinstance(term, Const) else solution[term.name]
                for term in terms
            )

    def _old_relation(self, signature, relations):
        """The relation as it stood before this update, rebuilt from the change.

        Only overdeletion needs this, and only for the relations a stratum
        actually reads, so it is built on demand rather than snapshotted: most
        updates never reconstruct anything at all.
        """
        cached = self._old.get(signature)
        if cached is None:
            added, removed = self._changes[signature]
            current = relations[signature].tuples
            cached = self._wrap(signature, (current - added) | removed)
            self._old[signature] = cached
        return cached

    def _wrap(self, signature, tuples):
        """A throwaway relation holding just ``tuples``, to join a delta against."""
        from .engine import Relation  # deferred: engine imports this module

        return Relation(signature[0], signature[1], tuples)

    def _count_iteration(self):
        self.iterations += 1
        if self.iterations > self.engine.max_iterations:
            raise EvaluationError(
                "incremental update did not converge after %d iterations; the "
                "program is probably generating new values through arithmetic"
                % self.engine.max_iterations
            )


# --------------------------------------------------------------------------
# Helpers
# --------------------------------------------------------------------------


def _positive(body, position):
    """``body`` with the negated literal at ``position`` read as a positive one."""
    literal = body[position]
    return body[:position] + (Literal(literal.atom, False),) + body[position + 1 :]


def _body_signatures(rules):
    """Every predicate these rules read, positively, negatively or aggregated."""
    found = set()
    for rule in rules:
        positive, negative = body_predicates(rule.body)
        found |= positive | negative
    return found


def _recursive_positions(rules, predicates):
    """Rules that read their own stratum, with the positions where they do."""
    out = []
    for rule in rules:
        positions = [
            position
            for position, literal in enumerate(rule.body)
            if isinstance(literal, Literal)
            and not literal.negated
            and literal.atom.signature in predicates
        ]
        if positions:
            out.append((rule, positions))
    return out
