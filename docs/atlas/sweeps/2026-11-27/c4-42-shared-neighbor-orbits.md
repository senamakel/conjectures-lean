# Shared-neighbor graph orbits in the four-degree-eight case

The six degree-six common neighbors are indexed by the unordered pairs of
degree-eight vertices. Consider the graph induced on these six witnesses. If
two witnesses adjacent to the same vertex shared a degree-eight endpoint,
they would give two distinct common neighbors of the vertex and that endpoint.
This is forbidden by C4-freeness. Thus two neighbors of any witness must carry
complementary pair labels. In particular the induced graph has maximum degree
two. Along a path, labels at distance two must be complementary, so a simple
path cannot contain five vertices. A triangle would require three pairwise
complementary labels. A four-cycle is forbidden by the original hypothesis.
These conditions leave only path components with at most four vertices.

Run `python3 scripts/c4_42_shared_neighbor_orbits.py` to exhaust the
2^15 simple labeled graphs on the six witnesses. The program checks both the
distinct-root condition and C4-freeness, and groups survivors by permutations
of the four degree-eight vertices. This enumeration ends after every mask
has been visited once. It takes under one CPU second on the build box.

| Edges | Labeled patterns | Orbits |
| ---: | ---: | ---: |
| 0 | 1 | 1 |
| 1 | 15 | 2 |
| 2 | 57 | 5 |
| 3 | 63 | 6 |
| 4 | 18 | 2 |
| Total | 154 | 16 |

These are complete cases for the two constraints on the induced graph.
Whether any representative extends to a 42-vertex, 138-edge C4-free graph
remains open. The enumeration produces no SAT result or Lean certificate.

## Rooted SAT instances

Use `python3 scripts/encode_c4_42_k4_canonical.py --shared-neighbor-case 16 .lake/case-16.cnf`
to emit the last case. Case numbers follow the census output, from 1 to 16.
Each case fixes all 15 edges among the six witnesses before emitting clauses.
The shared-neighbor orbit reduction permutes all four roots, while the separate
matching reduction distinguishes root 0. Applying both independently can lose
cases, so the encoder accepts only one of the two switches at a time.
