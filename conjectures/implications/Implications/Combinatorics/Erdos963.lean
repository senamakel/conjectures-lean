import Mathlib

/-!
# Erdős 963 (ii) ⇒ its variant for positive reals

The statements are copied word for word from formal-conjectures (commit `9097e2f`),
`FormalConjectures/ErdosProblems/963.lean`, with the definition `Erdos963.f` from the same file
(Apache-2.0, © 2025 The Formal Conjectures Authors):

* `Erdos963.erdos_963.parts.ii` (research open), stated here as `Erdos963PartII`:
  `f(n) ≥ ⌊log₂ n⌋` for every `n ≥ 1`, where `f(n)` is the largest `k` such that every set of `n`
  reals has a dissociated subset of size at least `k`;
* `Erdos963.erdos_963.variants.positive` (research open), stated here as `Erdos963Positive`:
  every finite set `A` of positive reals has a dissociated subset of size at least
  `⌊log₂ |A|⌋`.

The docstring of `parts.ii` says the positive variant "follows from this statement". The proof
needs no sign trick: the set of admissible `k` in the definition of `f(n)` is bounded by `n`, so
its supremum `f(n)` is attained, and every `n`-element set (positive or not) has a dissociated
subset of size at least `f(n) ≥ ⌊log₂ n⌋`. The positivity hypothesis is not used. (The docstring
also notes the stronger fact that `parts.ii` gives `⌊log₂ |A|⌋ + 1` for positive sets, via
`A ∪ (−A)`; that is not proved here.)
-/

namespace Implications.Combinatorics.Erdos963

/-- Verbatim from formal-conjectures `9097e2f`, `Erdos963.f`: the largest `k` such that every
set `A ⊂ ℝ` with `n` elements has a dissociated subset with at least `k` elements. -/
noncomputable def f (n : ℕ) : ℕ :=
  sSup {k : ℕ | ∀ A : Finset ℝ, A.card = n →
    ∃ B ⊆ A, k ≤ B.card ∧ AddDissociated (B : Set ℝ)}

/-- Verbatim from formal-conjectures `9097e2f`, `Erdos963.erdos_963.parts.ii`. -/
def Erdos963PartII : Prop := ∀ n : ℕ, 1 ≤ n → Nat.log 2 n ≤ f n

/-- Verbatim from formal-conjectures `9097e2f`, `Erdos963.erdos_963.variants.positive`. -/
def Erdos963Positive : Prop :=
    ∀ A : Finset ℝ, (∀ a ∈ A, 0 < a) →
      ∃ B ⊆ A, Nat.log 2 A.card ≤ B.card ∧ AddDissociated (B : Set ℝ)

/-- The supremum defining `f n` is attained: every `n`-element set of reals has a dissociated
subset with at least `f n` elements. -/
theorem exists_dissociated_of_card_eq {n : ℕ} (A : Finset ℝ) (hA : A.card = n) :
    ∃ B ⊆ A, f n ≤ B.card ∧ AddDissociated (B : Set ℝ) := by
  have hne : ({k : ℕ | ∀ A : Finset ℝ, A.card = n →
      ∃ B ⊆ A, k ≤ B.card ∧ AddDissociated (B : Set ℝ)}).Nonempty :=
    ⟨0, fun A' _ => ⟨∅, Finset.empty_subset _, Nat.zero_le _, by simp⟩⟩
  have hbdd : BddAbove {k : ℕ | ∀ A : Finset ℝ, A.card = n →
      ∃ B ⊆ A, k ≤ B.card ∧ AddDissociated (B : Set ℝ)} := by
    refine ⟨n, fun m hm => ?_⟩
    obtain ⟨A', hA'⟩ := Infinite.exists_subset_card_eq ℝ n
    obtain ⟨B, hBA, hmB, -⟩ := hm A' hA'
    exact hmB.trans ((Finset.card_le_card hBA).trans hA'.le)
  exact Nat.sSup_mem hne hbdd A hA

/-- **Erdős 963 (ii) ⇒ the positive-reals variant.** -/
theorem erdos963Positive_of_partII (h : Erdos963PartII) : Erdos963Positive := by
  intro A _
  rcases Nat.eq_zero_or_pos A.card with h0 | hpos
  · exact ⟨∅, Finset.empty_subset _, by simp [h0], by simp⟩
  · obtain ⟨B, hBA, hfB, hB⟩ := exists_dissociated_of_card_eq A rfl
    exact ⟨B, hBA, (h A.card hpos).trans hfB, hB⟩

end Implications.Combinatorics.Erdos963
