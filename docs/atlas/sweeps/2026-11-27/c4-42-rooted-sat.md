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
