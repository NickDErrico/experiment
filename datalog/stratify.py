"""Predicate dependency analysis and stratification.

Negation and aggregation are only well-defined when the predicate being negated
is *completely* known before the negating rule runs.  We guarantee that by
partitioning predicates into numbered strata such that

* a rule's head is never in a lower stratum than any predicate in its body, and
* a predicate reached through negation or an aggregate is in a *strictly*
  lower stratum than the head.

Recursion through negation makes such a numbering impossible, and that is
exactly the case we reject.
"""

from __future__ import annotations

from .errors import StratificationError
from .syntax import body_predicates


class DependencyGraph:
    """Predicate-level dependency graph built from a program's rules."""

    def __init__(self):
        self.nodes = set()
        self.edges = {}  # signature -> set of signatures it depends on
        self.negative = set()  # (head, body) pairs crossing a negation

    def add_node(self, signature):
        self.nodes.add(signature)
        self.edges.setdefault(signature, set())

    def add_edge(self, head, dependency, negated=False):
        self.add_node(head)
        self.add_node(dependency)
        self.edges[head].add(dependency)
        if negated:
            self.negative.add((head, dependency))

    def dependencies(self, signature):
        return self.edges.get(signature, set())


def build_graph(rules):
    """Build the dependency graph for a sequence of rules."""
    graph = DependencyGraph()
    for rule in rules:
        head = rule.head.signature
        graph.add_node(head)
        positive, negative = body_predicates(rule.body)
        for dependency in positive:
            graph.add_edge(head, dependency, negated=False)
        for dependency in negative:
            graph.add_edge(head, dependency, negated=True)
    return graph


def strongly_connected_components(graph):
    """Tarjan's algorithm, iterative so deep graphs cannot blow the stack.

    Components are returned in reverse topological order: a component is
    emitted only after every component it depends on, which is precisely the
    order we want for stratum assignment.
    """
    index_of = {}
    lowlink = {}
    on_stack = set()
    stack = []
    result = []
    counter = 0

    for root in sorted(graph.nodes):
        if root in index_of:
            continue
        # Each work item is (node, iterator over its successors).
        work = [(root, iter(sorted(graph.dependencies(root))))]
        index_of[root] = lowlink[root] = counter
        counter += 1
        stack.append(root)
        on_stack.add(root)

        while work:
            node, successors = work[-1]
            advanced = False
            for successor in successors:
                if successor not in index_of:
                    index_of[successor] = lowlink[successor] = counter
                    counter += 1
                    stack.append(successor)
                    on_stack.add(successor)
                    work.append((successor, iter(sorted(graph.dependencies(successor)))))
                    advanced = True
                    break
                if successor in on_stack:
                    lowlink[node] = min(lowlink[node], index_of[successor])
            if advanced:
                continue

            work.pop()
            if lowlink[node] == index_of[node]:
                component = []
                while True:
                    member = stack.pop()
                    on_stack.discard(member)
                    component.append(member)
                    if member == node:
                        break
                result.append(component)
            if work:
                parent = work[-1][0]
                lowlink[parent] = min(lowlink[parent], lowlink[node])

    return result


def stratify(rules):
    """Assign each predicate a stratum number.

    Returns ``(strata, stratum_of)`` where ``strata`` is a list of sets of
    predicate signatures ordered by evaluation order, and ``stratum_of`` maps a
    signature to its index in that list.

    Raises :class:`~datalog.errors.StratificationError` if the program recurses
    through negation or aggregation.
    """
    graph = build_graph(rules)
    components = strongly_connected_components(graph)

    component_of = {}
    for position, component in enumerate(components):
        for node in component:
            component_of[node] = position

    stratum_of_component = [0] * len(components)

    for position, component in enumerate(components):
        members = set(component)
        level = 0
        for node in component:
            for dependency in graph.dependencies(node):
                negated = (node, dependency) in graph.negative
                if dependency in members:
                    if negated:
                        raise StratificationError(
                            _cycle_message(component, node, dependency)
                        )
                    continue
                other = stratum_of_component[component_of[dependency]]
                level = max(level, other + (1 if negated else 0))
        stratum_of_component[position] = level

    depth = (max(stratum_of_component) + 1) if stratum_of_component else 0
    strata = [set() for _ in range(depth)]
    stratum_of = {}
    for position, component in enumerate(components):
        level = stratum_of_component[position]
        for node in component:
            strata[level].add(node)
            stratum_of[node] = level
    return strata, stratum_of


def _cycle_message(component, node, dependency):
    members = ", ".join("%s/%d" % sig for sig in sorted(component))
    return (
        "%s/%d depends negatively on %s/%d, but they are mutually recursive "
        "(cycle: %s). Programs that recurse through negation or aggregation "
        "have no stratified model." % (node + dependency + (members,))
    )
