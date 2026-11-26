import Mathlib

/-!
# Exchange lemmas for the lower and upper bounds of Algorithm 1

Let `L` be "the first `n` primes outside `Y`" and `F` the prime factors of `p - 1`, with
`|F| = |L|`, `F ∩ Y = ∅`. Every element of `F \ L` exceeds every element of `L`. Then:

* `∏ L ≤ ∏ F` (`prod_le_prod_of_dominates`), so `p ≥ 1 + ∏ L`;
* for `M ⊆ L` and `S ⊆ F` with `|S| = |M|` and `S \ M` disjoint from `L`,
  `Σ_S 1/q ≤ Σ_M 1/q` (`sum_inv_le_of_dominates`).

Both follow by comparing the two symmetric differences, which have the same size and where every
element on one side is at least every element on the other.
-/

namespace Grosswald.Combi

open Finset

lemma prod_le_of_ge {A B : Finset ℕ} (hc : A.card = B.card) (h : ∀ a ∈ A, ∀ b ∈ B, b ≤ a) :
    ∏ b ∈ B, b ≤ ∏ a ∈ A, a := by
  rcases B.eq_empty_or_nonempty with hB | hB
  · subst hB
    simp only [prod_empty]
    rw [card_empty, card_eq_zero] at hc
    subst hc
    simp
  set m := B.max' hB
  calc ∏ b ∈ B, b ≤ m ^ B.card := prod_le_pow_card _ _ _ fun b hb => le_max' B b hb
    _ = m ^ A.card := by rw [hc]
    _ ≤ ∏ a ∈ A, a := pow_card_le_prod _ _ _ fun a ha => h a ha m (max'_mem B hB)

lemma sum_inv_le_of_ge {A B : Finset ℕ} (hc : A.card = B.card) (hB : ∀ b ∈ B, 0 < b)
    (h : ∀ a ∈ A, ∀ b ∈ B, b ≤ a) : ∑ a ∈ A, 1 / (a : ℝ) ≤ ∑ b ∈ B, 1 / (b : ℝ) := by
  rcases B.eq_empty_or_nonempty with hB' | hB'
  · subst hB'
    rw [card_empty, card_eq_zero] at hc
    subst hc
    simp
  set m := B.max' hB'
  have hm : 0 < (m : ℝ) := by exact_mod_cast hB m (max'_mem B hB')
  calc ∑ a ∈ A, 1 / (a : ℝ) ≤ ∑ _a ∈ A, 1 / (m : ℝ) := by
        refine sum_le_sum fun a ha => ?_
        have : (m : ℝ) ≤ a := by exact_mod_cast h a ha m (max'_mem B hB')
        exact one_div_le_one_div_of_le hm this
    _ = ∑ _b ∈ B, 1 / (m : ℝ) := by simp [hc]
    _ ≤ ∑ b ∈ B, 1 / (b : ℝ) := by
        refine sum_le_sum fun b hb => ?_
        have hb0 : (0 : ℝ) < b := by exact_mod_cast hB b hb
        have : (b : ℝ) ≤ m := by exact_mod_cast le_max' B b hb
        exact one_div_le_one_div_of_le hb0 this

lemma card_sdiff_eq {F L : Finset ℕ} (h : F.card = L.card) : (F \ L).card = (L \ F).card := by
  have h1 := card_sdiff_add_card_inter F L
  have h2 := card_sdiff_add_card_inter L F
  rw [inter_comm] at h2
  omega

/-- `∏ L ≤ ∏ F` when `|F| = |L|` and every element of `F \ L` exceeds all of `L`. -/
lemma prod_le_prod_of_dominates {F L : Finset ℕ} (hc : F.card = L.card)
    (hdom : ∀ q ∈ F, q ∉ L → ∀ l ∈ L, l < q) : ∏ l ∈ L, l ≤ ∏ q ∈ F, q := by
  rw [← prod_inter_mul_prod_sdiff L F, ← prod_inter_mul_prod_sdiff F L, inter_comm]
  apply Nat.mul_le_mul_left
  apply prod_le_of_ge (card_sdiff_eq hc)
  intro a ha b hb
  exact (hdom a (mem_sdiff.mp ha).1 (mem_sdiff.mp ha).2 b (mem_sdiff.mp hb).1).le

/-- `Σ_S 1/q ≤ Σ_M 1/q` under the exchange hypotheses. -/
lemma sum_inv_le_of_dominates {S M L : Finset ℕ} (hML : M ⊆ L) (hc : S.card = M.card)
    (hpos : ∀ l ∈ L, 0 < l) (hdom : ∀ q ∈ S, q ∉ M → ∀ l ∈ L, l < q) :
    ∑ q ∈ S, 1 / (q : ℝ) ≤ ∑ q ∈ M, 1 / (q : ℝ) := by
  rw [← sum_inter_add_sum_sdiff S M, ← sum_inter_add_sum_sdiff M S, inter_comm]
  gcongr ?_ + ?_
  · exact le_rfl
  apply sum_inv_le_of_ge (card_sdiff_eq hc)
  · intro b hb; exact hpos b (hML (mem_sdiff.mp hb).1)
  intro a ha b hb
  exact (hdom a (mem_sdiff.mp ha).1 (mem_sdiff.mp ha).2 b (hML (mem_sdiff.mp hb).1)).le

end Grosswald.Combi
