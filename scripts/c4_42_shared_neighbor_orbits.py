#!/usr/bin/env python3
"""Enumerate shared-neighbor graphs allowed by unique two-step witnesses."""

from collections import Counter
from itertools import combinations, permutations

ROOTS = tuple(range(4))
PAIRS = tuple(combinations(ROOTS, 2))
EDGES = tuple(combinations(range(len(PAIRS)), 2))


def allowed(edges):
    """Require C4-freeness and distinct root incidences at each vertex."""
    seen_roots = [set() for _ in PAIRS]
    neighbors = [set() for _ in PAIRS]
    for u, v in edges:
        neighbors[u].add(v)
        neighbors[v].add(u)
        for vertex, neighbor in ((u, v), (v, u)):
            roots = PAIRS[neighbor]
            if not seen_roots[vertex].isdisjoint(roots):
                return False
            seen_roots[vertex].update(roots)
    return all(len(neighbors[u] & neighbors[v]) <= 1 for u, v in EDGES)


def rename(edges, image):
    return tuple(sorted(tuple(sorted((image[u], image[v]))) for u, v in edges))


def shared_neighbor_orbits():
    """Return representatives and orbit sizes, ordered by edge count and labels."""
    root_actions = [
        tuple(PAIRS.index(tuple(sorted((p[u], p[v])))) for u, v in PAIRS)
        for p in permutations(ROOTS)
    ]
    orbits = Counter()
    for mask in range(1 << len(EDGES)):
        edges = tuple(edge for i, edge in enumerate(EDGES) if mask & (1 << i))
        if allowed(edges):
            orbits[min(rename(edges, image) for image in root_actions)] += 1

    return tuple(sorted(orbits.items(), key=lambda item: (len(item[0]), item[0])))


def main():
    orbits = shared_neighbor_orbits()
    counts = Counter()
    for edges, size in orbits:
        counts[len(edges)] += size
        text = " ".join(
            f"{a}{b}-{c}{d}" for u, v in edges
            for (a, b), (c, d) in [(PAIRS[u], PAIRS[v])]
        )
        print(f"{size:2}  {text or '(empty)'}")
    print("Labeled counts by edge count:", dict(sorted(counts.items())))
    print(f"{sum(counts.values())} labeled patterns, {len(orbits)} orbits")


if __name__ == "__main__":
    main()
