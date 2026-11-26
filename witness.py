"""Construct nine wild edges for a proper 13-edge-coloring of K13.

Supply a JSON list with one integer color per edge in lexicographic order
(0,1), (0,2), ..., (11,12). With no argument, check a cyclic example in
each of the two cases of the reduction.
"""
import argparse
import json
from itertools import combinations
from pathlib import Path


VERTICES = tuple(range(13))
EDGES = tuple(combinations(VERTICES, 2))


def matchings(colors):
    if len(colors) != len(EDGES) or len(set(colors)) != 13:
        raise ValueError("Expected 78 edge colors with exactly 13 distinct labels.")
    by_label = {}
    for edge, color in zip(EDGES, colors):
        by_label.setdefault(color, []).append(edge)
    result = {}
    for edges in by_label.values():
        ends = [v for edge in edges for v in edge]
        if len(ends) != 12 or len(set(ends)) != 12:
            raise ValueError("Each color must consist of six disjoint edges.")
        missing, = set(VERTICES) - set(ends)
        result[missing] = edges
    if set(result) != set(VERTICES):
        raise ValueError("The missing vertices must all be distinct.")
    return result


def connected(edges):
    adjacency = [set() for _ in VERTICES]
    for a, b in edges:
        adjacency[a].add(b)
        adjacency[b].add(a)
    reached = {0}
    pending = [0]
    while pending:
        for v in adjacency[pending.pop()] - reached:
            reached.add(v)
            pending.append(v)
    return len(reached) == 13


def splits(points):
    for pair in combinations(points[1:], 2):
        first = (points[0], *pair)
        rest = tuple(v for v in points if v not in first)
        for pair2 in combinations(rest[1:], 2):
            second = (rest[0], *pair2)
            yield first, second, tuple(v for v in rest if v not in second)


def witness(colors, case=None):
    matches = matchings(colors)
    label = {edge: c for c, edges in matches.items() for edge in edges}
    for block in combinations(VERTICES, 4):
        labels = {label[e] for e in combinations(block, 2)}
        k = len(labels.intersection(block))
        if len(labels) != 6 or k > 1 or (case is not None and k != case):
            continue
        remaining = tuple(v for v in VERTICES if v not in block)
        for parts in splits(remaining):
            wild = [(part[0], v) for part in (block, *parts) for v in part[1:]]
            if all(connected(wild + matching) for matching in matches.values()):
                return block, k, parts, wild
        raise AssertionError("Eligible four-set with no working split.")
    raise ValueError("No suitable four-set for the requested case.")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("color_file", type=Path, nargs="?")
    args = parser.parse_args()
    if args.color_file:
        colors = json.loads(args.color_file.read_text(encoding="utf-8"))
        cases = (None,)
    else:
        # The edge ab gets color (a+b)/2 in the field with 13 elements.
        colors = [7 * (a+b) % 13 for a, b in EDGES]
        cases = (0, 1)
    for case in cases:
        block, k, parts, wild = witness(colors, case)
        print(f"k={k}, blocks={(block, *parts)}")
        print(f"{len(wild)} wild edges connect all 13 colors: {wild}")
