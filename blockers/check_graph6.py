"""Cross-check the maximum-link census with McKay's complete graph6 atlas."""

from collections import Counter
from hashlib import sha256
from itertools import combinations
from pathlib import Path

VERTICES = tuple(range(8))
PAIRS = tuple((i, j) for j in VERTICES for i in range(j))
TRIPLES = tuple(combinations(VERTICES, 3))
ATLAS_SHA256 = "546a249902101c97d3aa590f93e53366854bd0a6f405aa59bdb32d25c57f845a"


def complementary_triples():
    """For each pair xy, list the ten unordered ways to split the other six."""
    lookup = {t: i for i, t in enumerate(TRIPLES)}
    result = {}
    for pair in PAIRS:
        others = sorted(set(VERTICES) - set(pair))
        partitions = []
        for two in combinations(others[1:], 2):
            t = (others[0], *two)
            remaining = tuple(v for v in others if v not in t)
            partitions.append((lookup[t], lookup[remaining]))
        result[pair] = partitions
    return result


CUTS = complementary_triples()


def parse_graph6(line):
    if len(line) != 6 or line[0] != ord("G"):
        raise ValueError("Expected graph6 record on eight points")
    # The format stores the adjacency triangle most-significant bit first.
    bits = "".join(f"{c - 63:06b}" for c in line[1:])
    return {p for p, b in zip(PAIRS, bits) if b == "1"}


def possible(edges, degrees, limit, max_degree):
    """Cover uncovered partitions by selecting at most limit more triples."""
    if any(d > max_degree or d + limit < 2 for d in degrees):
        return False
    if not edges:
        return True
    if limit == 0:
        return False

    # No single choice covers two vertex-disjoint pairs of triple indices.
    used = set()
    degree = Counter()
    for a, b in edges:
        if a not in used and b not in used:
            used.update((a, b))
            if len(used) > 2 * limit:
                return False
        degree[a] += 1
        degree[b] += 1

    a, b = max(edges, key=lambda ab: degree[ab[0]] + degree[ab[1]])
    if degree[a] < degree[b]:
        a, b = b, a
    # Every solution hits {a,b}. If a has more neighbors than the budget,
    # omitting a would require selecting all of them.
    choices = (a,) if degree[a] > limit else (a, b)
    for t in choices:
        updated = list(degrees)
        for v in TRIPLES[t]:
            updated[v] += 1
        residual = [e for e in edges if t not in e]
        if possible(residual, updated, limit - 1, max_degree):
            return True
    return False


def main():
    data = Path(__file__).with_name("graph8.g6").read_bytes()
    if sha256(data).hexdigest() != ATLAS_SHA256:
        raise ValueError("Unexpected graph atlas checksum")
    records = data.splitlines()
    totals = Counter()
    survivors = Counter()
    for index, line in enumerate(records, start=1):
        link = parse_graph6(line)
        d = len(link)
        if not 10 <= d <= 19:
            continue
        totals[d] += 1
        degrees = [sum(v in e for e in link) for v in VERTICES]
        missing = [p for p in PAIRS if p not in link]
        cuts = [cut for p in missing for cut in CUTS[p]]
        if possible(cuts, degrees, 35 - d, d):
            survivors[d] += 1
            support = {v for p in missing for v in p}
            print(f"survivor: line {index}, link degree {d}, missing edges {missing}")
            if d not in (18, 19) or len(support) != 5:
                raise ValueError("Unexpected survivor shape")
    if len(records) != 12346 or survivors != {18: 1, 19: 1}:
        raise ValueError("Unexpected atlas or census result")
    print(f"Examined {sum(totals.values())} eligible links in {len(records)} atlas records")
    print("Tallies by degree:", sorted(totals.items()))
    print("Survivors by degree:", sorted(survivors.items()))


if __name__ == "__main__":
    main()
