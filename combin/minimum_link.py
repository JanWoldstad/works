"""Classify small blockers of partitions of nine points into triples (stdlib only)."""

from collections import Counter
from itertools import combinations, permutations, product
from math import comb, factorial


def bit_members(mask):
    while mask:
        lowest = mask & -mask
        yield lowest.bit_length() - 1
        mask ^= lowest


def pair_bit(u, v):
    if u > v:
        u, v = v, u
    return 1 << (v * (v - 1) // 2 + u)


def relabel(graph, n):
    """Choose a relabeling, minimizing over vertices tied by colour refinement."""
    neighbors = [0] * n
    for u, v in combinations(range(n), 2):
        if graph & pair_bit(u, v):
            neighbors[u] |= 1 << v
            neighbors[v] |= 1 << u
    cells = [tuple(range(n))]
    while True:
        cell_masks = [sum(1 << v for v in cell) for cell in cells]
        groups = []
        for cell in cells:
            by_counts = {}
            for v in cell:
                key = tuple((neighbors[v] & mask).bit_count() for mask in cell_masks)
                by_counts.setdefault(key, []).append(v)
            groups.extend(tuple(by_counts[key]) for key in sorted(by_counts))
        if len(groups) == len(cells):
            break
        cells = groups
    # Vertices having identical neighbours outside their pair can be exchanged
    # freely; if every pair in a cell does, one ordering already suffices.
    choices = []
    for cell in cells:
        twins = all((neighbors[u] ^ neighbors[v]) & ~((1 << u) | (1 << v)) == 0
                    for u, v in combinations(cell, 2))
        choices.append([cell] if twins else permutations(cell))
    best = None
    for parts in product(*choices):
        order = [u for part in parts for u in part]
        code = sum(pair_bit(i, j) for i, j in combinations(range(n), 2)
                   if neighbors[order[i]] & (1 << order[j]))
        if best is None or code < best:
            best = code
    return best


def link_types():
    graphs = {0}
    for n in range(2, 9):
        graphs = {relabel(graph | star << comb(n - 1, 2), n)
                  for graph in graphs for star in range(1 << (n - 1))
                  if graph.bit_count() + star.bit_count() <= 11}
    return sorted(graphs)


def expected_link_counts():
    """Independent orbit counts via Burnside, grouped by permutation cycle type."""
    n = 8
    edges = list(combinations(range(n), 2))
    edge_index = {edge: i for i, edge in enumerate(edges)}

    def cycle_sizes(perm):
        unused = set(range(len(perm)))
        while unused:
            v = min(unused)
            length = 0
            while v in unused:
                unused.remove(v)
                length += 1
                v = perm[v]
            yield length

    fixed_by_type = {}
    totals = [0] * 12
    for perm in permutations(range(n)):
        kind = tuple(sorted(cycle_sizes(perm)))
        if kind not in fixed_by_type:
            action = [edge_index[tuple(sorted((perm[u], perm[v])))] for u, v in edges]
            polynomial = [1] + [0] * 11
            for length in cycle_sizes(action):
                for j in range(11, length - 1, -1):
                    polynomial[j] += polynomial[j - length]
            fixed_by_type[kind] = polynomial
        for j, value in enumerate(fixed_by_type[kind]):
            totals[j] += value
    return [v // factorial(n) for v in totals]


POINTS = frozenset(range(9))
INNER = tuple(combinations(range(8), 3))
TRIPLES = tuple(combinations(range(9), 3))
CONTAINING = [sum(1 << i for i, t in enumerate(INNER) if v in t) for v in range(8)]
SPACES = [frozenset(t for t in TRIPLES if set(t) <= set(points))
          for points in combinations(POINTS, 7)]
FOURS = [frozenset(t for t in TRIPLES if len(set(t) & set(points)) >= 2)
         for points in combinations(POINTS, 4)]
SPLITS = [(a, b, tuple(sorted(POINTS - set(a) - set(b))))
          for a in TRIPLES if 8 in a
          for b in combinations(sorted(POINTS - set(a)), 3) if b[0] == min(POINTS - set(a))]


def classify_link(link):
    root = {(u, v, 8) for u, v in combinations(range(8), 2) if link & pair_bit(u, v)}
    d = len(root)
    root_incidence = [sum(v in t for t in root) for v in range(8)]
    conflict = [0] * len(INNER)
    for j, right in enumerate(INNER):
        for i, left in enumerate(INNER[:j]):
            if set(left).isdisjoint(right):
                x, y = sorted(POINTS - set(left) - set(right) - {8})
                if (x, y, 8) not in root:
                    conflict[i] |= 1 << j
                    conflict[j] |= 1 << i
    counts = Counter()

    def record(selected):
        family = root | {INNER[i] for i in bit_members(selected)}
        if any(all(t not in family for t in split) for split in SPLITS):
            raise ValueError("Cover does not block every partition")
        if any(space <= family for space in SPACES):
            counts["seven-set"] += 1
        elif any(four <= family for four in FOURS):
            counts["four-set"] += 1
        else:
            raise ValueError(f"Unclassified blocker: {sorted(family)}")

    def finish(selected, free, slots):
        # Degree constraints apply to every vertex. Visit all allowed subsets
        # of free, including the empty set and sets strictly smaller than slots.
        deficit = 0
        for v in range(8):
            degree = root_incidence[v] + (CONTAINING[v] & selected).bit_count()
            if degree > 19 or degree + min(slots, (CONTAINING[v] & free).bit_count()) < d:
                return
            deficit += max(0, d - degree)
        if deficit > 3 * slots:
            return
        if not deficit:
            record(selected)
        if slots:
            while free:
                take = free & -free
                free ^= take
                finish(selected | take, free, slots - 1)

    def covers(active, selected, free, slots):
        counts["nodes"] += 1
        if slots < 0:
            return
        # Split only on vertices in uncovered edges. Isolated vertices can
        # be picked or omitted independently at the end.
        pivot = None
        neighbors = 0
        for i in bit_members(active):
            peers = conflict[i] & active
            if not peers:
                active ^= 1 << i
                free |= 1 << i
            elif peers.bit_count() > neighbors.bit_count():
                pivot, neighbors = i, peers
        if pivot is None:
            finish(selected, free, slots)
            return
        for v in range(8):
            degree = root_incidence[v] + (CONTAINING[v] & selected).bit_count()
            if degree > 19 or degree + (CONTAINING[v] & (active | free)).bit_count() < d:
                return
        # Disjoint conflict edges must be covered by different selected vertices.
        packing = 0
        rest = active
        while rest:
            take = rest & -rest
            rest ^= take
            peers = conflict[take.bit_length() - 1] & rest
            if peers:
                rest ^= peers & -peers
                packing += 1
        if packing > slots:
            return
        pivot_bit = 1 << pivot
        covers(active ^ pivot_bit, selected | pivot_bit, free, slots - 1)
        if neighbors.bit_count() <= slots:
            covers(active ^ (pivot_bit | neighbors), selected | neighbors, free,
                   slots - neighbors.bit_count())

    covers((1 << len(INNER)) - 1, 0, 0, 35 - d)
    return counts


def main():
    graphs = link_types()
    expected = expected_link_counts()
    observed = Counter(g.bit_count() for g in graphs)
    if [observed[d] for d in range(12)] != expected:
        raise ValueError("Root graph inventory disagrees with Burnside's lemma")
    print("d links search_nodes seven_set_leaves four_set_leaves", flush=True)
    for d in range(12):
        counts = Counter()
        for graph in graphs:
            if graph.bit_count() == d:
                counts.update(classify_link(graph))
        print(d, observed[d], counts["nodes"], counts["seven-set"], counts["four-set"], flush=True)
    print(f"PASS: classified every blocker with at most 35 triples and maximum degree at most 19; {len(graphs)} link types.")


if __name__ == "__main__":
    main()
