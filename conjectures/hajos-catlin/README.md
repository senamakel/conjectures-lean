# Hajós' conjecture is false, in Lean (Catlin 1979)

Hajós conjectured in 1961 that every graph with chromatic number at least `k` contains a
subdivision of the complete graph `K_k`. This package is a complete Lean proof of Catlin's
disproof (P. A. Catlin, "Hajós' graph-coloring conjecture: variations and counterexamples",
*J. Combin. Theory Ser. B* 26 (1979), 268–274): the lexicographic product `C₅[K₃]` has
chromatic number at least `8` and contains no subdivision of `K₈`. Lean checks it from the three
standard axioms, with no `native_decide`. The theorem is formal-conjectures'
`HajosConjecture.hajos_conjecture`, statement unchanged. Literature label: *known* (refuted by
Catlin 1979; Erdős and Fajtlowicz 1981 showed almost every graph is a counterexample). Refutation
route **c** (a disproof published on paper, not yet in Lean).

## Headline theorems

```lean
theorem HajosConjecture.hajos_conjecture : ¬
    ∀ {V : Type} [Fintype V] (G : SimpleGraph V) (k : ℕ),
      (k : ℕ∞) ≤ G.chromaticNumber → ContainsSubdivision (completeGraph (Fin k)) G

theorem HajosConjecture.hajos_conjecture.variants.catlin_eight : CatlinVariant 8
-- CatlinVariant 8 unfolds to
--   ∃ (V : Type) (_ : Fintype V) (G : SimpleGraph V),
--     (8 : ℕ∞) ≤ G.chromaticNumber ∧ ¬ ContainsSubdivision (completeGraph (Fin 8)) G

theorem HajosCatlin.eight_le_chromaticNumber : (8 : ℕ∞) ≤ catlin.chromaticNumber
theorem HajosCatlin.not_containsSubdivision :
    ¬ ContainsSubdivision (completeGraph (Fin 8)) catlin
```

`HajosConjecture.hajosConjectureFalse : HajosConjectureFalse` is the same theorem against the
copied statement in `HajosCatlin/Statement.lean`.

## Tier and provenance

All theorems are **tier D**: closed statements with no hypotheses, proved here from Mathlib alone.

The statement is
[`FormalConjectures/Wikipedia/HajosConjecture.lean`](https://github.com/google-deepmind/formal-conjectures/blob/9097e2f90e66d2f6244209cb1c07f7120d17ec53/FormalConjectures/Wikipedia/HajosConjecture.lean)
at commit `9097e2f`, where `hajos_conjecture` is `research solved` with body `sorry` and no
`formal_proof` link. `IsSubdivisionModel` and `ContainsSubdivision` are copied word for word
into `HajosCatlin/Statement.lean`: an injective map of the branch vertices, and for each edge of
`K_k` a path whose interior (`support.tail.dropLast`) avoids the branch vertices and is disjoint
from the interiors of the other edges' paths. `hajos_conjecture` in `HajosCatlin/Main.lean`
carries the formal-conjectures statement unchanged.

The graph is ours: `HajosCatlin.catlin` on `Fin 5 × Fin 3`, with `(i, a) ~ (j, b)` when
`i = j ∧ a ≠ b`, or `j = i + 1`, or `i = j + 1` (addition in `Fin 5`).

## Axioms

```
'HajosConjecture.hajos_conjecture' depends on axioms: [propext, Classical.choice, Quot.sound]
'HajosConjecture.hajosConjectureFalse' depends on axioms: [propext, Classical.choice, Quot.sound]
'HajosConjecture.hajos_conjecture.variants.catlin_eight' depends on axioms: [propext, Classical.choice, Quot.sound]
```

The three finite facts (independence number 2 over `15³` triples, a few `Fin 5` identities, and
the arithmetic check over `4⁵` column vectors) are proved by `decide`, which the kernel checks;
there is no `native_decide`. Reproduce with `lake env lean scripts/Axioms.lean`.

## Proof outline

1. **`χ ≥ 8`** (`HajosCatlin/Graph.lean`). Any three distinct vertices contain an adjacent pair
   (`catlin_indep_three`, `decide`). A 7-colouring of 15 vertices has a colour class of size 3
   (`Fintype.exists_lt_card_fiber_of_mul_lt_card`, `7·2 < 15`), which is impossible.
2. **Walks cross the middle column** (`HajosCatlin/NoSubdivision.lean`, `walk_cross`). Two
   vertices are non-adjacent exactly when their columns differ by `±2`. A walk from column
   `c − 1` to column `c + 1` either meets column `c`, or avoids it; then column steps are at most
   one on the line `c+4, c+3, c+2, c+1`, and a discrete intermediate value lemma (`walk_ivt`)
   gives vertices in columns `c + 2` and `c + 3`. So the path's interior meets column `c` or has
   at least two vertices (`two_le`: `2 ≤ |interior| + [interior meets column c]`).
3. **Counting.** Let `a c ≤ 3` be the number of branch vertices in column `c` (`∑ a c = 8`). The
   non-adjacent branch pairs with middle column `c` number `a(c−1)·a(c+1)` (`S f c`). Their path
   interiors consist of free vertices (`interior_subset`) and are pairwise disjoint
   (`interior_disjoint`), so their sizes add up to at most `15 − 8 = 7` (`sum_interior_le`). The
   pairs of middle column `c` whose interior meets column `c` each use a distinct free vertex of
   that column, so there are at most `min (a(c−1)a(c+1)) (3 − a c)` of them (`card_E1_add`).
   Summing step 2 gives

   `2 ∑_c a(c−1)·a(c+1) ≤ 7 + ∑_c min (a(c−1)·a(c+1)) (3 − a c)`.
4. **Finite check** (`arith`). For all `a ∈ {0,…,3}⁵` with sum `8` the left side exceeds the
   right; the smallest gap is at `a = (0, 0, 2, 3, 3)`, where the left side is `12` and the
   right side `7`. Checked by `decide` over `4⁵` vectors.
5. **Assembly** (`HajosCatlin/Main.lean`). Apply the conjecture to `catlin` and `k = 8`.

## Deviations from the literature

Catlin's paper gives counterexamples for every `k ≥ 7`. Only `k = 8` is proved here, which is all
the headline statement needs. formal-conjectures' `hajos_conjecture.variants.catlin` (every
`k ≥ 7`) is proved at `k = 8` only (`catlin_eight`); the other `k`, and `k = 7` in particular,
need Catlin's other graphs and are not done. The other two variants in the file,
`variants.le_four` (Dirac 1952, a positive theorem) and `variants.five_six` (open), are out of
scope. The certificate in step 3–4 is our own counting argument; Catlin's paper was not read.

## Prior Lean work

Searched on 2026-11-26: Mathlib at the pin (no Hajós, subdivision or topological-minor
development under `Combinatorics/`), formal-conjectures at `9097e2f` (statement with `sorry`, no
`formal_proof`), and GitHub code search for `hajos`, `Catlin` and `ContainsSubdivision` in Lean
files. The only other hit is facebookresearch/atlas-lean
`v1/Atlas/ProbabilisticMethodsInCombinatorics/code/Chapter5/Hajos.lean` (with a mirror in
math-proof/lemma), whose `hajos_conjecture_counterexample` follows Erdős–Fajtlowicz and takes the
probability bound `probKtSubdiv` as a hypothesis. We found no unconditional Lean refutation.

## Building

Lean `v4.36.0`, Mathlib `fc4f59e577feb1a4956671bc04ac18aaaf8cd842`.

```
lake build HajosCatlin
lake env lean scripts/Axioms.lean
```

A clean build of the package takes about 30 s wall (18 s CPU) on top of the Mathlib cache; each
module takes under 10 s.

## This result needs no RH

The proof imports nothing beyond Mathlib, so there is no `Unconditional/` version.

## Credits

Built by the OpenHuman agents. `HajosCatlin/Statement.lean` copies definitions and statement
bodies from google-deepmind/formal-conjectures (commit `9097e2f`, Apache-2.0); see `NOTICE`.
