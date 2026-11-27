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

## Common-neighbor AMO benchmark protocol (written before the run)

For every unordered endpoint pair among labels 1..41, create 39 indicator
variables, one for each possible common neighbor. Add only the implication
`edge(u,x) ∧ edge(v,x) → indicator(u,v,x)`, then a sequential at-most-one
counter over the 39 indicators. The implication direction is deliberate: for
any valid edge assignment, choose each indicator to equal the actual
conjunction; conversely, two actual common neighbors force two true indicators
and violate AMO. Thus the projected edge assignments are equivalent to the
direct four-literal clauses, with 39 implication clauses plus 113 sequential
counter clauses per pair (versus 741 direct clauses per pair before duplicate
pair normalization, or 303,810 unique clauses overall).

Before SAT, exhaustively compare the direct relation and existential AMO
extension for all edge assignments with up to four possible common neighbors.
Then generate one formula with `--compact-degree-count
--compact-common-neighbor`; keep the old default and its hashes unchanged. Use
the installed CaDiCaL 2.1.2 with a 120-second limit and LRAT output, and stop at
SAT, complete UNSAT, or UNKNOWN. Do not rerun or extend the limit. Preserve the
formula, log, model or trace under `.lake/c4-42-rooted-sat/`. Any SAT model needs
an independent graph check. An UNSAT result requires Lean LRAT replay and an
encoding-to-graph proof.

The handshake identity and existing cap imply that the degree-eight count is
one of 0..4, with corresponding non-root `(n6,n7,n8)` profiles
`(17,24,0)`, `(18,22,1)`, `(19,20,2)`, `(20,18,3)`, `(21,16,4)`. Separate exact
`--degree-eight-count k` instances for k=0..4 are a possible proof split, but
this benchmark uses the combined cap and does not run those five cases.

## Common-neighbor AMO benchmark result

The exhaustive projection check passed for every edge assignment with zero to
four possible common neighbors. The old default formula still hashes to
`72fd863a9e29ca2422c129f2e885bba2a7343c9fb2a47dc482764aeae8b985a5`; the prior
compact direct-clause formula still hashes to
`66b84c521e0d6a0eb5dd7fe7749bb0e9da3415314d81e3c620f880503ebecbc4`.

The combined handshake and common-neighbor AMO formula has 79,194 variables,
184,200 clauses, 3,053,323 bytes and SHA-256
`3579071c047015ea7ec371fdb884682e27f0bf2d45e757f16b172115dd88d7bb`. The AMO
block contributes 124,640 clauses across 820 endpoint pairs: 39 implication
clauses and 113 sequential-counter clauses per pair. Relative to the previous
compact direct-clause formula, this adds 63,140 auxiliary variables while
removing 179,170 clauses and 4,486,428 bytes. The default options and both
previous formula hashes are unchanged.

The single CaDiCaL 2.1.2 run hit its 120 s real-time limit after 117.88 s
process CPU, with 922,757 conflicts, 1,133,616,237 propagations and 101.34 MB
peak RSS. It returned `UNKNOWN`, exit 0, and left a 738 MB partial LRAT trace;
there is no model and no complete proof. The smaller clause count did not settle
the case within this budget.

The script now supports `--degree-eight-count k` for k=0..4. Under the compact
handshake condition, fixing n8=k also forces n7=24−2k and n6=17+k among the
41 non-root vertices. This gives five exhaustive proof cases, but none was run
in this screen. A future proof must check all five cases and replay every proof;
the present combined-cap result remains only `UNKNOWN`.

## k=4 incidence benchmark protocol (written before the run)

The parent proof now establishes the k=4 incidence profile in Lean
(`C4DegreeEightMultiplicity`): each of four degree-eight vertices has seven
degree-six neighbors; each of 22 degree-six vertices has one or two degree-eight
neighbors; exactly six have two and the other 16 have one. These incidences
total 28. Use the existing degree-six root and labels 1..6 for its neighbors,
preserving the previously justified complete labeling symmetry. The additional
CNF constraints are exact degree-class conjunctions and exact threshold counts:
degree-eight vertices have exactly seven degree-six neighbors, degree-six
vertices have one or two degree-eight neighbors, and exactly six degree-six
vertices have multiplicity two. Also forbid degree-eight/degree-eight edges,
as follows from the checked degree cap lemma. These are necessary conditions,
so they retain every graph in the k=4 case. The auxiliary incidence flags are
constrained to equal their edge and degree-class conjunctions; the degree
threshold circuits are exact. Therefore an edge projection satisfying this
strengthened formula is still a graph satisfying the base formula.

Generate only the distinct k=4 strengthened formula with
`--deduplicate-c4 --compact-degree-count --compact-common-neighbor
--degree-eight-count 4 --k4-incidence`. Preserve the output under
`.lake/c4-42-rooted-sat/`. Run the existing CaDiCaL 2.1.2 binary once with a
120-second real-time limit and LRAT output. Stop on a model, complete UNSAT, or
UNKNOWN at the cap; do not rerun this instance or the earlier combined AMO
instance. Independently validate any model. A solver UNSAT result remains
incomplete until Lean checks its LRAT trace and a formal bridge connects this
exact encoder to the graph clauses. The checkable k=4 theorem replaces solver
work to reconstruct the incidence structure; it does not establish that this
SAT instance is UNSAT.

## k=4 incidence benchmark result

The distinct k=4 DIMACS has 99,290 variables and 258,637 clauses, 3,285,810
bytes, and SHA-256
`d6448208afa8948e2a277ad8baba2e4f6b49fbff41f5cc267c48eda9177260ee`.
The previous combined AMO instance was not rerun. CaDiCaL 2.1.2 returned
`UNKNOWN` at 120.00 seconds real time (114.34 seconds process CPU), after
1,002,195 conflicts and 825,225,357 propagations; peak resident memory was
515.10 MB. The partial binary LRAT trace is 776,499,763 bytes, SHA-256
`b3785957d0c684a4b78aacdb877e4d83e838750bee684212da527150ef79b8e3`.
There is no model and no complete proof. The incidence theorem reduces the
search but did not settle this case under the cap. The canonical encoding below
uses the newly checked pair-witness, private-neighbor, and distinct-owner
structure.

## Canonical k=4 encoding and bounded protocol (written before the run)

The canonical encoder uses labels 0..3 for the four D8 vertices; 4..9 for the
six unique D6 witnesses indexed by pairs `(01,02,03,12,13,23)`; 10..25 for
four private D6 neighbors per D8; 26..29 for the four distinct D7 owners; and
30..41 for the remaining twelve D7 vertices. Every qualifying graph can be
relabeled into this form: assign its four D8 vertices arbitrarily, then use
the pair-witness theorem, private-neighbor theorem, and distinct-owner theorem
to assign the corresponding labels. No sorting or extra symmetry restriction
is imposed. The four D8 neighborhoods are then fully fixed (three shared D6,
four private D6, one owner D7 each), eliminating all 158 edge variables
incident to a D8 and leaving the 703 edges among labels 4..41.

For every 4-set, the formula emits the three distinct C4 clauses and simplifies
them against the fixed edges. It adds the checked at-least-one common-neighbor
clause for each D8 `h` and each `x != h`; the four-cycle clauses already imply
at most one. In particular, when `x` is a neighbor of `h`, this requires an
edge inside `N(h)`, and C4-freeness makes those edges a perfect matching. The
encoder does not guess a matching. Exact local low-vertex degrees (6 for the
22 D6 labels, 7 for the 16 D7 labels) force the edge count by handshake: their
degree sum is 244, the four fixed D8 vertices add 32, so total degree is 276
and the graph has 138 edges. The implementation reuses `Cnf` and its exact
unary threshold circuit from `encode_c4_42_rooted_138.py`.

Generate `.lake/c4-42-k4-canonical/canonical.cnf` from
`scripts/encode_c4_42_k4_canonical.py`; check the label scheme and confirm the
previous rooted encoder's default digest remains
`72fd863a9e29ca2422c129f2e885bba2a7343c9fb2a47dc482764aeae8b985a5`. Run the
existing CaDiCaL 2.1.2 binary once with `--lrat --checkproof=2 -t 120`, writing
the log and LRAT only under `.lake/c4-42-k4-canonical/`. Stop at SAT, complete
UNSAT, or UNKNOWN at the cap; do not repeat or vary parameters. A SAT model
requires an independent graph check. UNSAT requires Lean LRAT replay and the
encoder-to-graph bridge; UNKNOWN is only a bounded screen.

## Four cases for the matching on N(0): bounded protocol (written before run)

The unique-codegree theorem makes the induced graph on the eight neighbors of
D8 label 0 a perfect matching. Its vertices are shared labels `{4,5,6}`, private
labels `{10,11,12,13}`, and owner label `26`. The label-preserving action is
`S3 × S4`: permuting D8 labels 1..3 permutes shared labels 4..6, and the four
private neighbors of D8 label 0 may be permuted independently; owner 26 stays
fixed. `--check-matching-orbits` enumerates all 105 perfect matchings under all
144 group elements and verifies four orbits, with sizes 9, 36, 24, and 36.
The listed representatives in cases 1..4 lie in distinct orbits, so the union
of the four CNF cases is complete. Cases are disjoint because the induced
matching is unique and each branch fixes all 28 possible edges within N(0) to
one particular matching.

For each case, edge lookup treats the four matching edges as true and the
other 24 edges within N(0) as false. This removes those 28 edge variables and
simplifies C4 clauses and degree counters. Every branch has 8,643 variables
and 229,626 clauses, against 9,195 variables and 258,093 clauses for the
canonical formula without matching normalization. This should help by exposing
the forced neighborhood pattern as constants before propagation; it does not
assume which partner any vertex has except for the selected exhaustive orbit.

Run only case 1 as a bounded feasibility screen. Generate
`.lake/c4-42-k4-matching-cases/case1.cnf`; run the existing CaDiCaL 2.1.2
binary with `--lrat --checkproof=2 -t 120` and a 120-second per-process CPU
limit (`ulimit -t 120`). Stop on SAT, complete UNSAT, or either the solver's
120-second real-time cap or the process CPU cap. Store CNF, log, and LRAT only
under `.lake/c4-42-k4-matching-cases/`. Do not rerun case 1 or run cases 2..4
in this screen. This one result cannot rule out the graph: a full UNSAT claim
requires all four disjoint cases to have complete LRAT proofs and Lean replay,
plus the canonical encoder bridge. A SAT model must be checked independently.

### Case 1 result

The matching orbit checker passed: 105 matchings split into the four distinct
orbits of sizes 9, 36, 24, and 36. The unbranched canonical CNF retained its
prior hash `3e25c572d4ae8b08925b518a87dc0402b46878e7c4994d89665bd3559ce83051`.
Case 1 has 8,643 variables and 229,626 clauses, SHA-256
`871b1b5cd59bed4485331926c986340e19f41308f7fbc040c2404d8ed0d65573`.
CaDiCaL 2.1.2 returned `UNKNOWN` at 120.01 seconds real time (118.82 seconds
process CPU), after 2,684,873 conflicts and 259,554,075 propagations; peak RSS
was 515.10 MB. Its partial binary LRAT trace is 425,834,000 bytes, SHA-256
`fc54ba38582c13f86baff5680c752500f07563806258538ab3a601d7ecbc4372`.
There is no model or complete proof. Only case 1 was run; cases 2..4 remain
untouched, so this screen says nothing conclusive about the full graph claim.
