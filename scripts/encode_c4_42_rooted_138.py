#!/usr/bin/env python3
"""Emit an exact CNF for a C4-free (42, 138) graph rooted at a degree-six vertex.

Vertex 0 is the root and has neighbors 1..6. All remaining vertices have full
degree 6..8; at most four have degree 8. Degree order is canonicalized within
the two root-relative blocks 1..6 and 7..41. The root contributes six of the
138 edges, so the emitted graph on 1..41 has exactly 132 edges.

This script only emits DIMACS. It does not invoke a SAT solver or execute any
external artifact.
"""

from __future__ import annotations

import argparse
from itertools import combinations
from pathlib import Path


class Cnf:
    def __init__(self) -> None:
        self.nvars = 0
        self.clauses: list[list[int]] = []

    def var(self) -> int:
        self.nvars += 1
        return self.nvars

    def clause(self, *lits: int | bool) -> None:
        out: list[int] = []
        for lit in lits:
            if isinstance(lit, bool):
                if lit:
                    return
                continue
            if -lit in out:
                return
            out.append(lit)
        self.clauses.append(out)

    def equivalent_atleast(self, inputs: list[int | bool], threshold: int) -> list[int | bool]:
        """Return exact threshold predicates: result[k] iff count(inputs) >= k."""
        def or_gate(a: int | bool, b: int | bool) -> int | bool:
            if a is True or b is True:
                return True
            if a is False:
                return b
            if b is False:
                return a
            y = self.var()
            self.clause(-a, y)
            self.clause(-b, y)
            self.clause(-y, a, b)
            return y

        prev: list[int | bool] = [True] + [False] * threshold
        for x in inputs:
            nxt: list[int | bool] = [True]
            for k in range(1, threshold + 1):
                a, b = prev[k], prev[k - 1]
                if a is True or (x is True and b is True):
                    y: int | bool = True
                elif x is False or b is False:
                    y: int | bool = a
                elif x is True:
                    y = or_gate(a, b)
                elif b is True:
                    y = or_gate(a, x)
                elif a is False:
                    y = self.var()
                    self.clause(-y, x)
                    self.clause(-y, b)
                    self.clause(y, -x, -b)
                else:
                    y = self.var()
                    # y <-> a OR (x AND b)
                    self.clause(-y, a, x)
                    self.clause(-y, a, b)
                    self.clause(-a, y)
                    self.clause(-x, -b, y)
                nxt.append(y)
            prev = nxt
        return prev

    def emit(self, path: Path) -> None:
        with path.open("w", newline="\n") as f:
            f.write(f"p cnf {self.nvars} {len(self.clauses)}\n")
            for clause in self.clauses:
                f.write(" ".join(map(str, clause)))
                f.write(" 0\n")


def build(
    deduplicate_c4: bool = False,
    compact_degree_count: bool = False,
) -> tuple[Cnf, dict[tuple[int, int], int]]:
    cnf = Cnf()
    edges: dict[tuple[int, int], int] = {}
    vertices = range(1, 42)
    for u, v in combinations(vertices, 2):
        edges[u, v] = cnf.var()

    def edge(u: int, v: int) -> int:
        return edges[min(u, v), max(u, v)]

    # C4-freeness in the graph remaining after root 0 is deleted: two vertices
    # cannot have two distinct common neighbors.
    for u, v in combinations(vertices, 2):
        others = [w for w in vertices if w != u and w != v]
        for x, y in combinations(others, 2):
            # The same four-cycle clause is also generated with {x,y} as the
            # distinguished pair. Exactly one orientation has u < x.
            if deduplicate_c4 and u > x:
                continue
            cnf.clause(-edge(u, x), -edge(v, x), -edge(u, y), -edge(v, y))

    # C4s through root 0: two root-neighbors cannot share any other neighbor.
    root_neighbors = range(1, 7)
    for u, v in combinations(root_neighbors, 2):
        for x in vertices:
            if x != u and x != v:
                cnf.clause(-edge(u, x), -edge(v, x))

    # The non-root graph has 132 edges; with the root's six edges this is 138.
    # Compact mode derives this from the handshake lemma: each of the 42 full
    # degrees lies in {6,7,8}, and sum(degree - 6) = 24 iff the graph has 138
    # edges. Since root 0 has degree six, its contribution is zero. The two
    # exact threshold flags for each remaining vertex are (degree >= 7) and
    # (degree >= 8); their total is precisely sum(degree - 6).
    edge_count: list[int | bool] | None = None
    if not compact_degree_count:
        edge_count = cnf.equivalent_atleast(list(edges.values()), 133)
        cnf.clause(edge_count[132])
        cnf.clause(-edge_count[133])

    degree_thresholds: dict[int, list[int | bool]] = {}
    degree_eight: list[int | bool] = []
    degree_excess_flags: list[int | bool] = []
    for v in vertices:
        incident: list[int | bool] = [edge(u, v) for u in vertices if u != v]
        incident.append(v <= 6)  # fixed edge (0,v)
        thresholds = cnf.equivalent_atleast(incident, 9)
        degree_thresholds[v] = thresholds
        # 1..6 have one fixed root edge, all others have none.
        high_plus_one = 9
        cnf.clause(thresholds[6])
        cnf.clause(-thresholds[high_plus_one])
        degree_eight.append(thresholds[8])
        degree_excess_flags.extend((thresholds[7], thresholds[8]))

    if compact_degree_count:
        # Exactly 24 true flags means total degree 252 + 24 = 276, hence 138
        # edges by the handshake lemma. This is equivalent to the 132-edge
        # induced graph condition because root 0 contributes six edges.
        excess_count = cnf.equivalent_atleast(degree_excess_flags, 25)
        cnf.clause(excess_count[24])
        cnf.clause(-excess_count[25])

    # The root itself has degree six. Degree sorting is valid under label
    # permutations that preserve the six root-neighbors as a block.
    for block in (list(range(1, 7)), list(range(7, 42))):
        for left, right in zip(block, block[1:]):
            for k in (7, 8):
                # If right has degree >= k, left must also have degree >= k.
                cnf.clause(-degree_thresholds[right][k], degree_thresholds[left][k])

    # Existing checked extremal degree-cap lemma: no more than four 8-degree
    # vertices occur in a 42-vertex, 138-edge C4-free graph under the deletion
    # bound. The fixed root has degree six, so it is absent from this list.
    at_most_five = cnf.equivalent_atleast(degree_eight, 5)
    cnf.clause(-at_most_five[5])
    return cnf, edges


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("output", type=Path, help="DIMACS path (keep generated data under .lake/)")
    parser.add_argument("--deduplicate-c4", action="store_true",
                        help="emit one copy of each opposite-pair C4 clause")
    parser.add_argument("--compact-degree-count", action="store_true",
                        help="derive the 138-edge count from degree flags via handshake")
    args = parser.parse_args()
    cnf, _ = build(args.deduplicate_c4, args.compact_degree_count)
    cnf.emit(args.output)
    print(f"wrote {args.output}: {cnf.nvars} variables, {len(cnf.clauses)} clauses")


if __name__ == "__main__":
    main()
