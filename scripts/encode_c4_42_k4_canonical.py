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
from itertools import combinations
from pathlib import Path

from encode_c4_42_rooted_138 import Cnf


def negate(lit: int | bool) -> int | bool:
    return not lit if isinstance(lit, bool) else -lit


def pair_labels() -> dict[tuple[int, int], int]:
    return {pair: 4 + i for i, pair in enumerate(combinations(range(4), 2))}


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


def build() -> Cnf:
    cnf = Cnf()
    fixed, neighborhoods = fixed_high_edges()
    edges: dict[tuple[int, int], int] = {}
    for u, v in combinations(range(4, 42), 2):
        edges[u, v] = cnf.var()

    def edge(u: int, v: int) -> int | bool:
        if u == v:
            return False
        pair = frozenset((u, v))
        if pair in fixed:
            return fixed[pair]
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
        fixed_degree = sum(v in neighborhoods[h] for h in range(4))
        required = target - fixed_degree
        inputs = [edge(v, w) for w in range(4, 42) if w != v]
        assert all(isinstance(lit, int) for lit in inputs)
        count = cnf.equivalent_atleast([int(lit) for lit in inputs], required + 1)
        cnf.clause(count[required])
        cnf.clause(negate(count[required + 1]))
    return cnf


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("output", type=Path, nargs="?",
                        help="DIMACS path (store generated data under .lake/)")
    parser.add_argument("--check-scheme", action="store_true",
                        help="check the fixed label partition and D8 neighborhoods")
    args = parser.parse_args()
    if args.check_scheme:
        check_scheme()
        return
    if args.output is None:
        parser.error("output is required unless --check-scheme is used")
    cnf = build()
    cnf.emit(args.output)
    print(f"wrote {args.output}: {cnf.nvars} variables, {len(cnf.clauses)} clauses")


if __name__ == "__main__":
    main()
