#!/usr/bin/env python3
"""Emit the canonical k=4 CNF for a C4-free (42, 138) graph.

Labels 0..3 are the degree-eight vertices; 4..9 are their six pairwise
degree-six common neighbors; 10..25 are the four private degree-six neighbors
of each degree-eight vertex; 26..29 are its four distinct degree-seven owners;
and 30..41 are the remaining degree-seven vertices. All D8 incident edges are
fixed from these proved neighborhoods, leaving only edges among labels 4..41.

This script emits DIMACS and does not invoke a SAT solver.
"""

from __future__ import annotations

import argparse
from itertools import combinations, permutations
from pathlib import Path

from encode_c4_42_rooted_138 import Cnf


def negate(lit: int | bool) -> int | bool:
    return not lit if isinstance(lit, bool) else -lit


def pair_labels() -> dict[tuple[int, int], int]:
    return {pair: 4 + i for i, pair in enumerate(combinations(range(4), 2))}


def matching_cases() -> tuple[tuple[tuple[int, int], ...], ...]:
    """The four representatives of matchings on N(0) under S3 x S4."""
    return (
        ((26, 4), (5, 6), (10, 11), (12, 13)),
        ((26, 4), (5, 10), (6, 11), (12, 13)),
        ((26, 10), (4, 11), (5, 12), (6, 13)),
        ((26, 10), (4, 5), (6, 11), (12, 13)),
    )


def check_matching_orbits() -> None:
    """Enumerate all 105 matchings and verify the four S3 x S4 orbits."""
    shared = (4, 5, 6)
    private = (10, 11, 12, 13)
    owner = 26
    vertices = tuple(sorted((*shared, *private, owner)))

    def all_matchings(remaining: tuple[int, ...]):
        if not remaining:
            yield ()
            return
        first = remaining[0]
        for index in range(1, len(remaining)):
            partner = remaining[index]
            rest = remaining[1:index] + remaining[index + 1:]
            for tail in all_matchings(rest):
                yield tuple(sorted(((first, partner), *tail)))

    def normalize(pairs: tuple[tuple[int, int], ...]) -> tuple[tuple[int, int], ...]:
        return tuple(sorted(tuple(sorted(pair)) for pair in pairs))

    matchings = {normalize(matching) for matching in all_matchings(vertices)}
    assert len(matchings) == 105

    # A permutation of D8 labels 1,2,3 induces the same permutation of the
    # shared witnesses 4,5,6. The private labels and owner are independent.
    actions = []
    for high_permutation in permutations((1, 2, 3)):
        shared_image = {4 + i: 4 + high_permutation[i] - 1 for i in range(3)}
        for private_permutation in permutations(private):
            image = (shared_image | dict(zip(private, private_permutation)) |
                     {owner: owner})
            actions.append(image)
    assert len(actions) == 144

    def act(matching: tuple[tuple[int, int], ...], image: dict[int, int]):
        return normalize(tuple((image[u], image[v]) for u, v in matching))

    unseen = set(matchings)
    orbits: list[set[tuple[tuple[int, int], ...]]] = []
    while unseen:
        seed = min(unseen)
        orbit = {act(seed, image) for image in actions}
        assert orbit <= unseen
        orbits.append(orbit)
        unseen -= orbit

    representatives = [normalize(case) for case in matching_cases()]
    representative_orbits = [next(i for i, orbit in enumerate(orbits)
                                   if representative in orbit)
                             for representative in representatives]
    assert len(orbits) == 4
    assert len(set(representative_orbits)) == 4
    assert sorted(map(len, orbits)) == [9, 24, 36, 36]
    assert sum(map(len, orbits)) == len(matchings)
    print("105 perfect matchings split into four S3×S4 orbits of sizes 9, 24, 36, 36")


def fixed_high_edges() -> tuple[dict[frozenset[int], bool], dict[int, list[int]]]:
    """Return all D8-incident edge constants and their fixed neighborhoods."""
    pairs = pair_labels()
    neighborhoods = {u: [] for u in range(4)}
    for (u, v), witness in pairs.items():
        neighborhoods[u].append(witness)
        neighborhoods[v].append(witness)
    for u in range(4):
        neighborhoods[u].extend(range(10 + 4 * u, 14 + 4 * u))
        neighborhoods[u].append(26 + u)

    fixed: dict[frozenset[int], bool] = {}
    for u in range(4):
        for v in range(4, 42):
            fixed[frozenset((u, v))] = v in neighborhoods[u]
        for v in range(u + 1, 4):
            fixed[frozenset((u, v))] = False
    return fixed, neighborhoods


def check_scheme() -> None:
    """Check the canonical label partition and fixed D8 neighborhood profile."""
    pairs = pair_labels()
    fixed, neighborhoods = fixed_high_edges()
    assert list(pairs.values()) == list(range(4, 10))
    assert set(range(4, 10)).isdisjoint(range(10, 26))
    assert set(range(10, 26)).isdisjoint(range(26, 30))
    assert set(range(26, 30)).isdisjoint(range(30, 42))
    assert set(range(4, 42)) == (set(pairs.values()) | set(range(10, 26)) |
                                 set(range(26, 30)) | set(range(30, 42)))
    for u in range(4):
        assert len(neighborhoods[u]) == 8
        assert len(set(neighborhoods[u])) == 8
        shared = {w for (a, b), w in pairs.items() if u in (a, b)}
        private = set(range(10 + 4 * u, 14 + 4 * u))
        owner = {26 + u}
        assert len(shared) == 3 and len(private) == 4 and len(owner) == 1
        assert set(neighborhoods[u]) == shared | private | owner
        assert all(fixed[frozenset((u, v))] for v in neighborhoods[u])
    assert sum(map(len, neighborhoods.values())) == 32
    print("canonical labels partition 42 vertices; each D8 has 3 shared, 4 private D6 and one owner D7")


def build(matching_case: int | None = None) -> Cnf:
    cnf = Cnf()
    fixed, neighborhoods = fixed_high_edges()
    matching_fixed: dict[frozenset[int], bool] = {}
    if matching_case is not None:
        if matching_case not in range(1, 5):
            raise ValueError("matching_case must be 1..4")
        n0 = neighborhoods[0]
        selected = {frozenset(pair) for pair in matching_cases()[matching_case - 1]}
        matching_fixed = {
            frozenset(pair): frozenset(pair) in selected
            for pair in combinations(n0, 2)
        }
    edges: dict[tuple[int, int], int] = {}
    for u, v in combinations(range(4, 42), 2):
        if frozenset((u, v)) in matching_fixed:
            continue
        edges[u, v] = cnf.var()

    def edge(u: int, v: int) -> int | bool:
        if u == v:
            return False
        pair = frozenset((u, v))
        if pair in fixed:
            return fixed[pair]
        if pair in matching_fixed:
            return matching_fixed[pair]
        return edges[min(u, v), max(u, v)]

    # The three distinct four-cycle edge sets on each four-vertex set.
    for a, b, c, d in combinations(range(42), 4):
        cycles = ((a, b, c, d, a), (a, b, d, c, a), (a, c, b, d, a))
        for cycle in cycles:
            cnf.clause(*(negate(edge(x, y))
                         for x, y in zip(cycle, cycle[1:])))

    # Every x != h has a common neighbor with each D8 vertex h. Four-cycle
    # clauses already give uniqueness, so these are only at-least-one clauses.
    # For another D8 vertex the fixed shared-pair edge satisfies the clause.
    for h in range(4):
        for x in range(42):
            if x != h:
                cnf.clause(*(edge(x, w) for w in neighborhoods[h]))

    # Exact low-vertex degrees. The fixed D8 incidences contribute 1 to a
    # private D6 / owner D7, 2 to a shared D6, and zero to other D7 vertices.
    # Thus all degrees, and hence 138 edges by handshake, are forced locally.
    targets: dict[int, int] = {v: 6 for v in range(4, 26)}
    targets.update({v: 7 for v in range(26, 42)})
    for v, target in targets.items():
        high_degree = sum(v in neighborhoods[h] for h in range(4))
        low_incidence = [edge(v, w) for w in range(4, 42) if w != v]
        fixed_low_degree = sum(lit is True for lit in low_incidence)
        required = target - high_degree - fixed_low_degree
        inputs = [lit for lit in low_incidence if not isinstance(lit, bool)]
        count = cnf.equivalent_atleast(inputs, required + 1)
        cnf.clause(count[required])
        cnf.clause(negate(count[required + 1]))
    return cnf


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("output", type=Path, nargs="?",
                        help="DIMACS path (store generated data under .lake/)")
    parser.add_argument("--check-scheme", action="store_true",
                        help="check the fixed label partition and D8 neighborhoods")
    parser.add_argument("--check-matching-orbits", action="store_true",
                        help="enumerate all matchings of N(0) under its S3×S4 relabelings")
    parser.add_argument("--matching-case", type=int, choices=range(1, 5),
                        help="fix one of four complete symmetry cases for the matching on N(0)")
    args = parser.parse_args()
    if args.check_scheme:
        check_scheme()
        return
    if args.check_matching_orbits:
        check_matching_orbits()
        return
    if args.output is None:
        parser.error("output is required unless --check-scheme is used")
    cnf = build(args.matching_case)
    cnf.emit(args.output)
    print(f"wrote {args.output}: {cnf.nvars} variables, {len(cnf.clauses)} clauses")


if __name__ == "__main__":
    main()
