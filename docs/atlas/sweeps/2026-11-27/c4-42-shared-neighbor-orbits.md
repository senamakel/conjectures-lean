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

## First solver screen

Test cases 15 and 16 first. They are the only orbit representatives with four
present shared edges, the maximum permitted by the local constraints. Present
edges trigger two-step uniqueness and exact-degree propagation, so these cases
may resolve faster than a split that fixes the root matching alone.

Generate exactly these two formulas with the encoder and run CaDiCaL 2.1.2
in parallel, with `--lrat --checkproof=2 -t 45`. Use an external 55-second
wall limit, a 50-second CPU limit, and 2 GiB limits on address space and output
file size per solver. Stop at SAT, UNSAT, a limit, or an error. The combined
CPU budget is 100 seconds. Independently verify a model or replay a complete
proof before counting a case as resolved.

Both formulas had 8,804 variables and 243,530 clauses. Both solvers reached
the configured wall limit and returned UNKNOWN with process exit code 0.

| Case | Wall seconds | CPU seconds | Conflicts | Propagations | Peak KiB | Partial LRAT bytes |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| 15 | 45.09 | 37.95 | 667,872 | 84,954,679 | 48,464 | 85,993,871 |
| 16 | 45.02 | 38.59 | 679,622 | 81,013,610 | 51,556 | 101,326,334 |

The DIMACS SHA-256 digests were:

- Case 15: `5a289361235a24442448909b27a2403ecc2b07de21ed560ebdd8ac4a55bc9d7a`
- Case 16: `9fec54b1978a8175b4ceaf2eb161cbd63da898081f82cf2ff0addba1cc9ae7fc`

The partial traces provide no certificate and no model was emitted. Cases
1–14 were outside the screen, and cases 15–16 remain unresolved at this cap.

## Shared and outside neighbor balance

For a nonroot vertex (v), write (r(v)) for its count of root neighbors,
(s(v)) for its count of shared-witness neighbors, (p(v)) for its count of
private degree-six and root-owned degree-seven neighbors, and (o(v)) for
its count of remaining degree-seven neighbors. Every root has a unique
common neighbor with (v). Counting these four witnesses with multiplicity
gives (2s(v)+p(v)=4), since a shared neighbor serves two roots. Counting
all neighbors gives (r(v)+s(v)+p(v)+o(v)=deg(v)). Therefore (s(v)le 2)
and
[
o(v)=deg(v)-r(v)-4+s(v).
]
The constant term is 0 for shared witnesses, 1 for private degree-six
vertices, 2 for the root-owned degree-seven vertices, and 3 for the
remaining degree-seven vertices.

Pass `--shared-outside-balance` to add these redundant clauses using exact
unary counters. It works with either symmetry split or the unrestricted
formula. The option is off by default, preserving earlier input hashes.
The gate encoding was exhaustively checked on 1,024 small input assignments
covering all four constant terms and both fixed Boolean values.

## Screen with shared and outside degree balance

The explicit degree-balance constraints can propagate the consequences of
fixed shared edges before a two-step witness is chosen. This screen tests
whether that makes any of the 16 cases resolve at a short cap. It uses the
shared-neighbor split and the balance option for every case, including the
two densest cases previously tested without balance.

Emit each formula with `--shared-neighbor-case N --shared-outside-balance`.
Run CaDiCaL 2.1.2 with `--lrat --checkproof=2 -t 60` and a 70-second
external wall timeout, a 65-second CPU limit and 2 GiB limits on address
space and output file size per case. Run at most eight solvers in parallel.
Stop each at SAT, UNSAT, a resource limit, or an error. The total solver
CPU budget is 1,040 seconds. Verify any SAT model or complete UNSAT trace
independently before marking a case resolved.
