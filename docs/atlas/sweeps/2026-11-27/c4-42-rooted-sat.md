# Rooted SAT screen for a 42-vertex, 138-edge C4-free graph

## Bounded search protocol (written before the solver run)

The target is the remaining `hno` obligation in `Implications/C4Extremal42.lean`:
rule out a C4-free graph on 42 vertices with 138 edges, equivalently a 41-vertex,
132-edge deletion graph with a compatible six-set. Fix a degree-six vertex as label
0 and its six neighbors as labels 1 through 6. The other 35 vertices are labels
7 through 41. The SAT instance uses one Boolean for each edge among labels 1..41,
requires 132 such edges, C4-freeness both within those labels and through root 0,
full degrees in 6..8, and at most four degree-eight vertices (the existing checked
degree cap). Within labels 1..6 and 7..41 separately, sort full degrees
nonincreasingly to remove valid permutations of those blocks.

Run only this first exact case. Use the already-installed CaDiCaL from the ignored
`.lake/polarity-sat/cadical-src/build/cadical`; cap at 120 CPU seconds. Stop on a
checked UNSAT result, a model, or the cap. Do not run parameter sweeps or increase
the cap in this screen. Preserve the DIMACS, solver log and any witness only under
`.lake/`; do not run or import code from Yan's archive. If SAT, independently
check the model as a labelled simple graph and report the counterexample. If UNSAT,
record that this is only a solver result until the trace is replayed in Lean and the
CNF-to-graph equivalence is proved. This is a feasibility screen for the reduction,
not a registry submission or public claim.

## Encoding plan

The fixed root contributes six edges, so its remaining graph has 41 vertices and
132 edges. For each pair of vertices in that remainder and pair of distinct
potential common neighbors, one four-literal clause forbids the four edges that
would form a C4. For each pair among root-neighbors 1..6 and each other remainder
vertex, a two-literal clause forbids a second common neighbor besides root 0.
Unary threshold circuits encode degree bounds and the global degree-eight cap;
the same degree thresholds encode the block sorting constraints.

This note distinguishes two trust gaps: solver output needs LRAT replay (the local
Lean standard-library checker is available), and the Boolean encoding still needs
a soundness/completeness proof connecting its satisfying assignments to the graph
statement. Label-fixing is complete because every candidate has a degree-six root;
its neighbors can be relabeled 1..6 and all other vertices 7..41. Sorting degrees
within either block is complete because arbitrary permutations within each block
preserve the root-neighbor set.

## First capped run

The first DIMACS was emitted before the opposite-pair deduplication described
below. It had 114,586 variables, 1,060,462 clauses, and SHA-256
`72fd863a9e29ca2422c129f2e885bba2a7343c9fb2a47dc482764aeae8b985a5`.
The encoder took 0.80 s wall time and 219,864 KB peak RSS. CaDiCaL 2.1.2 hit its
120 s real-time limit after 113.99 s process CPU, 107,474 conflicts and
651,354,304 propagations; result `UNKNOWN`, exit 0. It wrote a 103 MB partial
LRAT trace, which is not a proof and was not replayed. Thus the first screen
neither establishes UNSAT nor yields a model.

The original protocol called this a CPU cap, but CaDiCaL's `-t` option is a
real-time limit. The observed CPU use stayed below 120 s. The optional
`--deduplicate-c4` mode removes duplicate C4 clauses: swapping the two opposite vertex-pairs emits the
same clause twice, so requiring the first pair's lower endpoint to be smaller
retains exactly one copy and halves that block from 607,620 to 303,810 clauses.
The resulting instance had 756,652 clauses and the same normalized clause
set as the original. Its SHA-256 was
`96a0a88fe8c3570bdb0953d4616c4e10fe7fbb3566c3a7896f8863419ef31200`.
The solver measurement above is from the original instance.

## Compact handshake benchmark protocol (written before this run)

Generate one refined instance with both `--deduplicate-c4` and
`--compact-degree-count`. Keep the original default output untouched. Run the
already-installed CaDiCaL 2.1.2 once with a 120-second solver limit, enabling
LRAT output. Stop on a checked SAT model, a complete UNSAT trace, or UNKNOWN at
the cap; do not extend the limit or run parameter variants. Keep all generated
files in `.lake/c4-42-rooted-sat/`. Before solving, run the separate arithmetic
checker `scripts/check_c4_42_degree_handshake.py`; it exhausts the allowed degree
multiplicity profiles independently of the CNF generator. A SAT model must be
independently parsed and checked for edge count, degree window, degree-eight cap
and C4-freeness. An UNKNOWN result is only a bounded screen. An UNSAT result
counts only after Lean LRAT replay and a proof that the CNF faithfully encodes
the graph constraints.

## Compact benchmark result

The compact DIMACS had 16,054 variables and 363,370 clauses. Its SHA-256 was
`66b84c521e0d6a0eb5dd7fe7749bb0e9da3415314d81e3c620f880503ebecbc4`.
Independent regeneration matched this digest, and the arithmetic check covered
all 903 non-root degree multiplicity profiles. CaDiCaL returned `UNKNOWN`
after 120.02 seconds elapsed and 116.98 seconds user CPU, with 1,274,094
conflicts and 763,443,748 propagations. The partial trace contains
554,295,732 bytes. The solver returned neither a model nor a complete proof.

Lean's `C4Extremal42.c4Free_iff_rooted_cycle_clauses` proves that the
two graph-level clause families characterize four-cycle-freeness.
`C4Extremal42.edge_count_eq_138_iff_rooted_degree_flags` proves the compact
count condition. Both use only the standard axioms. The link from the exact
DIMACS variable allocation and threshold gates to these predicates remains
a separate proof obligation.
