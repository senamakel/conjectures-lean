#!/usr/bin/env python3
"""Enumerate shared-neighbor graphs allowed by unique two-step witnesses."""

from collections import Counter
from itertools import combinations, permutations

ROOTS = tuple(range(4))
PAIRS = tuple(combinations(ROOTS, 2))
EDGES = tuple(combinations(range(len(PAIRS)), 2))


def allowed(edges):
    """At each vertex, no two neighbors can share a root in their labels."""
    seen_roots = [set() for _ in PAIRS]
    for u, v in edges:
        for vertex, neighbor in ((u, v), (v, u)):
            roots = PAIRS[neighbor]
            if not seen_roots[vertex].isdisjoint(roots):
                return False
            seen_roots[vertex].update(roots)
    return True


def rename(edges, image):
    return tuple(sorted(tuple(sorted((image[u], image[v]))) for u, v in edges))


def main():
    root_actions = [
        tuple(PAIRS.index(tuple(sorted((p[u], p[v])))) for u, v in PAIRS)
        for p in permutations(ROOTS)
    ]
    orbits = Counter()
    counts = Counter()
    for mask in range(1 << len(EDGES)):
        edges = tuple(edge for i, edge in enumerate(EDGES) if mask & (1 << i))
        if allowed(edges):
            counts[len(edges)] += 1
            orbits[min(rename(edges, image) for image in root_actions)] += 1

    for edges, size in sorted(orbits.items(), key=lambda item: (len(item[0]), item[0])):
        text = " ".join(f"{PAIRS[u][0]}{PAIRS[u][1]}-{PAIRS[v][0]}{PAIRS[v][1]}" for u, v in edges)
        print(f"{size:2}  {text or '(empty)'}")
    print("Labeled counts by edge count:", dict(sorted(counts.items())))
    print(f"{sum(counts.values())} labeled patterns, {len(orbits)} orbits")


if __name__ == "__main__":
    main()
