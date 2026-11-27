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

| Case | Solver status | CPU seconds | DIMACS SHA-256 |
| ---: | --- | ---: | --- |
| 1 | UNSAT | 54.04 | `04e203c18d69cd5dfec8c5f23ad4b6a5ffe4cc5bd3a8d451520174f096911357` |
| 2 | UNKNOWN | 59.67 | `f1de4c6aa3eead03df374ccaf53bb16a2a3581f3796772cfa725b2c3f7127881` |
| 3 | UNKNOWN | 59.69 | `3087d03486f67c0d3cc5a535635e9e9e274b0c95db319eeb9ae70c6accc2ea9b` |
| 4 | UNKNOWN | 59.68 | `2b1330097e868eede8066c5bd8234539cab55c77bf43db97a4a7cfb9028a04ca` |
| 5 | UNKNOWN | 59.75 | `6f3677b9ae7faf8d50d05566faf03e8afbced1f6c22c9bf3366d224a97134551` |
| 6 | UNKNOWN | 59.53 | `8eb081f8a2e26ee0cb7fc4e5f23567ad6cfc48f5f087e3a30fe201bdf5728b7b` |
| 7 | UNKNOWN | 59.73 | `c2d368030bf3a67595368150fb64a66a85626edeeeee5c31a01b148d2f1fa261` |
| 8 | UNKNOWN | 59.67 | `d58c3b36b8c263ed306d59c7a4cf2607842ee8f545548706f51b948ab6f8438b` |
| 9 | UNKNOWN | 58.65 | `1a748303ba87b228f68a4145141660038cad296db47e900b49ba1fb0e048f0ca` |
| 10 | UNKNOWN | 59.51 | `f0f64634a252f52e4c8b04cffc88c2589115daa5a05e7fc3775640cec4b6142a` |
| 11 | UNKNOWN | 58.09 | `98289b2d9852dab36c8c11a96949002aec00bbaa06c6d9002eb9ac1cb3cc3f2f` |
| 12 | UNKNOWN | 59.27 | `3541e258e4e6ff72a0eb901a64b270bec775f8709704b877c6e02d49921afca6` |
| 13 | UNKNOWN | 59.21 | `ef59bb8f0e9fed2213fdd973c1900f1626211bf6aca59c53ee9ca4aafdd42e53` |
| 14 | UNKNOWN | 58.68 | `966255555e965ca8d2832950025f305e96839551111e0460e1df80886b3c17e5` |
| 15 | UNKNOWN | 58.02 | `2658683f689cb983c370a360654b2e0fbdc2f8cc66dc40a43e72fdecb7a9be8f` |
| 16 | UNKNOWN | 58.95 | `80a3974fa95930a0ca5aac09237d576d5288c4b5f1d7d7392e2224ca67cc23f8` |

Case 1, the empty shared-neighbor pattern, finished in 54.30 wall seconds.
It has 11,122 variables and 248,174 clauses. CaDiCaL exited 20 and emitted
a complete binary LRAT trace with SHA-256
`4abdfc93d8de33cbd13d096d2c9168bf30dacef5d45106230ae7739e0f6ecbf7`.
Running `lake env lean --run ../../scripts/check_dimacs_lrat.lean FORMULA TRACE`
from a built `conjectures/implications` checkout verified all 1,984,168 actions
in 31.81 wall seconds. This checks the concrete DIMACS formula. A Lean proof
that every empty-pattern graph gives a satisfying assignment to this exact
formula is still needed for an end-to-end graph theorem. Cases 2–16 returned
UNKNOWN and their partial traces certify no result.

The mathematical weighted count is independently formalized as
`C4RootWitnessCountIdentity.four_root_witness_weighted_count`. Lean reports
the standard axioms `propext`, `Classical.choice`, and `Quot.sound`.
