"""Check the two high-degree links left by the blocker enumeration."""

from itertools import combinations


def bit(i, j):
    return 1 << (j * (j - 1) // 2 + i)


def perfect_matchings(vertices):
    if not vertices:
        yield 0
        return
    first, *rest = vertices
    for partner in rest:
        others = [v for v in rest if v != partner]
        for remainder in perfect_matchings(others):
            yield bit(first, partner) | remainder


def check():
    vertices = tuple(range(8))
    all_edges = sum(bit(i, j) for i, j in combinations(vertices, 2))
    five_set = sum(bit(i, j) for i, j in combinations(range(5), 2))
    all_matchings = set(perfect_matchings(vertices))
    if len(all_matchings) != 105:
        raise ValueError("Incorrect number of perfect matchings of K8.")
    for degree, mask in [(18, 268434432), (19, 268434944)]:
        expected = all_edges ^ five_set
        if degree == 19:
            expected |= bit(3, 4)
        if mask != expected or mask.bit_count() != degree:
            raise ValueError("Link mask disagrees with its claimed graph.")
        matching = [m for m in all_matchings if m & mask == m]
        disjoint = sum(not (a & b) for a, b in combinations(matching, 2))
        if len(matching) != (0 if degree == 18 else 6) or disjoint:
            raise ValueError("Unexpected matching count.")
        if degree == 19 and not all(m & bit(3, 4) for m in matching):
            raise ValueError("An allowed matching avoided the unique edge on the five-set.")
        print(f"degree={degree} mask={mask} perfect_matchings={len(matching)} "
              f"edge_disjoint_pairs={disjoint}")


if __name__ == "__main__":
    check()
