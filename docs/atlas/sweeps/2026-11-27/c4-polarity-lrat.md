# LRAT replay for order-seven polarity deletions

27 November 2026. CaDiCaL 2.1.2 returned UNSAT for the symmetry-reduced model of a 138-edge, 42-vertex induced subgraph of the orthogonal polarity graph of `PG(2,7)`. Lean's standard-library LRAT checker replayed the resulting certificate. The graph-to-CNF correspondence below is a mathematical argument supported by executable input checks. The Lean checker certifies unsatisfiability of the emitted CNF.

The source graph has 57 vertices and 224 edges. Its eight absolute points have degree seven and all other vertices have degree eight. Deleting 15 vertices (D) leaves (104+e(D)+a(D)) edges, where (a(D)) counts the deleted absolute points. The required score is at least 34. A retained graph meeting the target also has minimum degree at least six, by the 132-edge bound on each 41-vertex deletion. [Polarity construction](https://arxiv.org/abs/1201.4912) · [41-vertex bound](https://doi.org/10.5281/zenodo.23334621)

- The deletion bits sum to 15. An edge bit equals the conjunction of its endpoint deletion bits. The edge bits and deletion bits for absolute points sum to at least 34.
- For a retained vertex (v), each ((d(v)-5))-subset of its neighbors has at least one retained member. This is exactly the minimum-degree-six constraint.
- The encoder enumerates 336 projective permutations induced by orthonormal bases over (mathbb F_7), checking each permutation and its preservation of the adjacency and absolute-point predicates. The lexicographic constraints choose a maximal deletion string in each orbit. A maximal feasible string satisfies every such constraint.
- The threshold circuit is defined by the equivalence that at least (k) true inputs after adding (x) means either at least (k) before, or (x) and at least (k-1) before. The lexicographic circuit tracks equality of the two prefixes. Exhaustive two-input truth-table checks of both gates passed.

The instance had 27,226 variables and 147,652 clauses. The UNSAT verdict took 0.97 seconds and 4,965 conflicts. The trace had 114,126 replayed actions. The result constrains this induced-subgraph family. It leaves the general 137–138 range open.

From the checkout root with Lean 4.36.0 and the Implications package cache available:

```sh
mkdir -p .lake/polarity-sat
python3 scripts/encode_c4_polarity_42_cnf.py --symmetry > .lake/polarity-sat/symmetry.cnf
cadical --lrat --checkproof=2 -t 30 .lake/polarity-sat/symmetry.cnf .lake/polarity-sat/symmetry.lrat
cd conjectures/implications
lake env lean --run ../../scripts/check_dimacs_lrat.lean ../../.lake/polarity-sat/symmetry.cnf ../../.lake/polarity-sat/symmetry.lrat
```

CaDiCaL uses exit code 20 for UNSAT. The checked files had these SHA-256 digests:

| File | SHA-256 |
|---|---|
| `symmetry.cnf` | `27e22fc68ac0734d9e10c6a0e058345bd9aa10ce4e1824bbc18853d6947cd1ea` |
| `symmetry.lrat` | `27a7d5286ec09732a7af553ea6b6138ae38fc637dc708f034a9e37c19e130dbe` |
