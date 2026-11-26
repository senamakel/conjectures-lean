import Mathlib

/-!
# Statement: Hajós' conjecture (1961)

Copied word for word from
[formal-conjectures](https://github.com/google-deepmind/formal-conjectures) at commit
`9097e2f90e66d2f6244209cb1c07f7120d17ec53`, file `FormalConjectures/Wikipedia/HajosConjecture.lean`
(Apache-2.0, © 2026 The Formal Conjectures Authors).

* `HajosConjecture.IsSubdivisionModel` and `HajosConjecture.ContainsSubdivision`: copied
  unchanged, docstrings included.
* `HajosConjecture.HajosConjectureFalse`: the statement of the theorem
  `HajosConjecture.hajos_conjecture` (`@[category research solved, AMS 5]`, body `sorry` there),
  with `theorem hajos_conjecture : P := by sorry` turned into `def HajosConjectureFalse : Prop := P`
  and `P` unchanged.
* `HajosConjecture.CatlinVariant k`: the body of `hajos_conjecture.variants.catlin (k) (hk : 7 ≤ k)`,
  as a predicate of `k` (the hypothesis `7 ≤ k` dropped; we prove it at `k = 8` only).

The only other changes are the ones needed outside formal-conjectures' build: `module`,
`public import FormalConjecturesUtil`, `@[expose] public section` and the `@[category …]`
attributes are dropped, and `import Mathlib` is used instead.
-/

open SimpleGraph

namespace HajosConjecture

variable {V W : Type*}

/-- A **subdivision model** of `H` in `G`: an injective map `f` of the vertices of `H` to
*branch vertices* of `G`, together with, for each edge `w w'` of `H`, a path in `G` from
`f w` to `f w'` whose internal vertices avoid all branch vertices and are disjoint from the
internal vertices of the paths of all other edges. -/
structure IsSubdivisionModel (H : SimpleGraph W) (G : SimpleGraph V) (f : W → V)
    (P : ∀ w w', H.Adj w w' → G.Walk (f w) (f w')) : Prop where
  injective : Function.Injective f
  isPath : ∀ w w' h, (P w w' h).IsPath
  internal_avoid : ∀ w w' h x, x ∈ (P w w' h).support.tail.dropLast → x ∉ Set.range f
  internal_disjoint : ∀ w₁ w₁' h₁ w₂ w₂' h₂, s(w₁, w₁') ≠ s(w₂, w₂') →
    ∀ x, x ∈ (P w₁ w₁' h₁).support.tail.dropLast → x ∉ (P w₂ w₂' h₂).support.tail.dropLast

/-- `G` contains a **subdivision** of `H` (i.e. `H` is a topological minor of `G`). -/
def ContainsSubdivision (H : SimpleGraph W) (G : SimpleGraph V) : Prop :=
  ∃ (f : W → V) (P : ∀ w w', H.Adj w w' → G.Walk (f w) (f w')), IsSubdivisionModel H G f P

/--
**Hajós' conjecture (1961) — disproved.** The statement of formal-conjectures'
`HajosConjecture.hajos_conjecture`, unchanged.

Hajós conjectured that every graph with chromatic number at least $k$ contains a subdivision of
$K_k$ (a strengthening of Hadwiger's conjecture). This is **false**: Catlin [Ca79] gave
counterexamples for every $k \ge 7$, and Erdős and Fajtlowicz [EF81] showed that almost all
graphs are counterexamples.
-/
def HajosConjectureFalse : Prop :=
  ¬ ∀ {V : Type} [Fintype V] (G : SimpleGraph V) (k : ℕ),
      (k : ℕ∞) ≤ G.chromaticNumber → ContainsSubdivision (completeGraph (Fin k)) G

/-- The body of formal-conjectures' `hajos_conjecture.variants.catlin (k) (hk : 7 ≤ k)`,
unchanged, as a predicate of `k`. -/
def CatlinVariant (k : ℕ) : Prop :=
  ∃ (V : Type) (_ : Fintype V) (G : SimpleGraph V),
      (k : ℕ∞) ≤ G.chromaticNumber ∧ ¬ ContainsSubdivision (completeGraph (Fin k)) G

end HajosConjecture
