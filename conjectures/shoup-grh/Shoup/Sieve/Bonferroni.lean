import Mathlib

/-!
# Truncated inclusion–exclusion (Bonferroni inequalities)

For a finite set `B` and weights `y : ℕ → ℝ`,
`G m B y = Σ_{T ⊆ B, |T| < m} (-1)^{|T|} ∏_{ℓ∈T} y ℓ` is the inclusion–exclusion expansion of
`∏_{ℓ∈B} (1 - y ℓ)` truncated below degree `m`, and `E m B y = Σ_{T ⊆ B, |T| = m} ∏_{ℓ∈T} y ℓ`
is the elementary symmetric function.

* `bonferroni`: for `0 ≤ y ≤ 1`, `(-1)^(m+1) (G m B y - ∏ (1 - y)) ≥ 0`; so `G m` is an upper
  bound for odd `m` and a lower bound for even `m`.
* `G_succ`: `G (m+1) = G m + (-1)^m E m`.
* `E_le`: `E m B y ≤ t^{-m} ∏ (1 + t y)` for `t > 0`, `y ≥ 0`.
* `E_div_prod_le`: `E m B y / ∏ (1 - y) ≤ t^{-m} exp((t + 2) Σ y)` for `0 ≤ y ≤ 1/2`.
-/

namespace Shoup.Sieve

open Finset

/-- Inclusion–exclusion for `∏_{ℓ∈B} (1 - y ℓ)`, truncated to the subsets of size `< m`. -/
noncomputable def G (m : ℕ) (B : Finset ℕ) (y : ℕ → ℝ) : ℝ :=
  ∑ T ∈ B.powerset, if T.card < m then (-1 : ℝ) ^ T.card * ∏ ℓ ∈ T, y ℓ else 0

/-- The elementary symmetric function of degree `m` of the `y ℓ`, `ℓ ∈ B`. -/
noncomputable def E (m : ℕ) (B : Finset ℕ) (y : ℕ → ℝ) : ℝ :=
  ∑ T ∈ B.powersetCard m, ∏ ℓ ∈ T, y ℓ

lemma G_zero (B : Finset ℕ) (y : ℕ → ℝ) : G 0 B y = 0 := by
  simp [G]

lemma G_empty (m : ℕ) (y : ℕ → ℝ) : G (m + 1) ∅ y = 1 := by
  simp [G]

lemma G_insert {x : ℕ} {B : Finset ℕ} (hx : x ∉ B) (m : ℕ) (y : ℕ → ℝ) :
    G (m + 1) (insert x B) y = G (m + 1) B y - y x * G m B y := by
  unfold G
  rw [Finset.sum_powerset_insert hx, sub_eq_add_neg, Finset.mul_sum, ← Finset.sum_neg_distrib]
  congr 1
  refine Finset.sum_congr rfl fun T hT => ?_
  have hxT : x ∉ T := fun h => hx (Finset.mem_powerset.mp hT h)
  rw [Finset.card_insert_of_notMem hxT, Finset.prod_insert hxT]
  by_cases h : T.card < m
  · rw [if_pos (by omega), if_pos h, pow_succ]; ring
  · rw [if_neg (by omega), if_neg h]; ring

/-- **Bonferroni inequalities.** -/
theorem bonferroni (B : Finset ℕ) (y : ℕ → ℝ) (hy : ∀ ℓ ∈ B, 0 ≤ y ℓ ∧ y ℓ ≤ 1) (m : ℕ) :
    0 ≤ (-1 : ℝ) ^ (m + 1) * (G m B y - ∏ ℓ ∈ B, (1 - y ℓ)) := by
  induction B using Finset.induction_on generalizing m with
  | empty =>
    rcases m with _ | m
    · simp [G_zero]
    · simp [G_empty]
  | insert x B hx ih =>
    have hyB : ∀ ℓ ∈ B, 0 ≤ y ℓ ∧ y ℓ ≤ 1 := fun ℓ h => hy ℓ (Finset.mem_insert_of_mem h)
    have hyx := hy x (Finset.mem_insert_self x B)
    have hPi : 0 ≤ ∏ ℓ ∈ B, (1 - y ℓ) :=
      Finset.prod_nonneg fun ℓ h => by linarith [(hyB ℓ h).2]
    rw [Finset.prod_insert hx]
    rcases m with _ | m
    · rw [G_zero]
      have : 0 ≤ (1 - y x) * ∏ ℓ ∈ B, (1 - y ℓ) := mul_nonneg (by linarith) hPi
      simp only [zero_add, pow_one]
      linarith
    · rw [G_insert hx]
      have h1 := ih hyB (m + 1)
      have h2 := ih hyB m
      have key : (-1 : ℝ) ^ (m + 1 + 1) *
          (G (m + 1) B y - y x * G m B y - (1 - y x) * ∏ ℓ ∈ B, (1 - y ℓ)) =
          (-1 : ℝ) ^ (m + 1 + 1) * (G (m + 1) B y - ∏ ℓ ∈ B, (1 - y ℓ)) +
          y x * ((-1 : ℝ) ^ (m + 1) * (G m B y - ∏ ℓ ∈ B, (1 - y ℓ))) := by
        rw [pow_succ (-1 : ℝ) (m + 1)]; ring
      rw [key]
      exact add_nonneg h1 (mul_nonneg hyx.1 h2)

/-- Odd truncation: an upper bound. -/
theorem prod_le_G_odd (B : Finset ℕ) (y : ℕ → ℝ) (hy : ∀ ℓ ∈ B, 0 ≤ y ℓ ∧ y ℓ ≤ 1) (k : ℕ) :
    ∏ ℓ ∈ B, (1 - y ℓ) ≤ G (2 * k + 1) B y := by
  have := bonferroni B y hy (2 * k + 1)
  rw [show 2 * k + 1 + 1 = 2 * (k + 1) by ring, pow_mul] at this
  norm_num at this
  linarith

/-- Even truncation: a lower bound. -/
theorem G_even_le_prod (B : Finset ℕ) (y : ℕ → ℝ) (hy : ∀ ℓ ∈ B, 0 ≤ y ℓ ∧ y ℓ ≤ 1) (k : ℕ) :
    G (2 * k + 2) B y ≤ ∏ ℓ ∈ B, (1 - y ℓ) := by
  have := bonferroni B y hy (2 * k + 2)
  rw [show 2 * k + 2 + 1 = 2 * (k + 1) + 1 by ring, pow_succ, pow_mul] at this
  norm_num at this
  linarith

lemma G_succ (m : ℕ) (B : Finset ℕ) (y : ℕ → ℝ) :
    G (m + 1) B y = G m B y + (-1 : ℝ) ^ m * E m B y := by
  unfold G E
  rw [Finset.powersetCard_eq_filter, Finset.sum_filter, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun T _ => ?_
  by_cases h : T.card < m
  · rw [if_pos (by omega), if_pos h, if_neg (by omega)]; ring
  · by_cases h' : T.card = m
    · rw [if_pos (by omega), if_neg h, if_pos h', h']; ring
    · rw [if_neg (by omega), if_neg h, if_neg h']; ring

lemma E_nonneg (m : ℕ) (B : Finset ℕ) (y : ℕ → ℝ) (hy : ∀ ℓ ∈ B, 0 ≤ y ℓ) :
    0 ≤ E m B y :=
  Finset.sum_nonneg fun T hT => Finset.prod_nonneg fun ℓ hℓ =>
    hy ℓ ((Finset.mem_powersetCard.mp hT).1 hℓ)

lemma E_one (B : Finset ℕ) (y : ℕ → ℝ) : E 1 B y = ∑ ℓ ∈ B, y ℓ := by
  simp [E, Finset.powersetCard_one]

lemma G_one (B : Finset ℕ) (y : ℕ → ℝ) : G 1 B y = 1 := by
  rw [show (1 : ℕ) = 0 + 1 from rfl, G_succ, G_zero]
  simp [E]

/-- `E m B y ≤ t^{-m} ∏ (1 + t y)`. -/
lemma E_le (m : ℕ) (B : Finset ℕ) (y : ℕ → ℝ) (hy : ∀ ℓ ∈ B, 0 ≤ y ℓ) {t : ℝ} (ht : 0 < t) :
    E m B y ≤ (∏ ℓ ∈ B, (1 + t * y ℓ)) / t ^ m := by
  rw [le_div_iff₀ (pow_pos ht m), Finset.prod_one_add]
  unfold E
  rw [Finset.sum_mul]
  calc ∑ T ∈ B.powersetCard m, (∏ ℓ ∈ T, y ℓ) * t ^ m
      = ∑ T ∈ B.powersetCard m, ∏ ℓ ∈ T, t * y ℓ := by
        refine Finset.sum_congr rfl fun T hT => ?_
        rw [Finset.prod_mul_distrib, Finset.prod_const, (Finset.mem_powersetCard.mp hT).2]
        ring
    _ ≤ ∑ T ∈ B.powerset, ∏ ℓ ∈ T, t * y ℓ := by
        refine Finset.sum_le_sum_of_subset_of_nonneg (fun T hT => Finset.mem_powerset.mpr (Finset.mem_powersetCard.mp hT).1) ?_
        intro T hT _
        exact Finset.prod_nonneg fun ℓ hℓ =>
          mul_nonneg ht.le (hy ℓ (Finset.mem_powerset.mp hT hℓ))

lemma exp_neg_two_mul_le {v : ℝ} (h0 : 0 ≤ v) (h1 : v ≤ 1 / 2) : Real.exp (-2 * v) ≤ 1 - v := by
  have h := Real.add_one_le_exp (2 * v)
  have hpos : 0 < Real.exp (2 * v) := Real.exp_pos _
  have : Real.exp (-2 * v) * Real.exp (2 * v) = 1 := by
    rw [← Real.exp_add]; simp
  nlinarith

/-- `∏ (1 - y) ≥ exp(-2 Σ y)` for `0 ≤ y ≤ 1/2`. -/
lemma exp_le_prod (B : Finset ℕ) (y : ℕ → ℝ) (hy : ∀ ℓ ∈ B, 0 ≤ y ℓ ∧ y ℓ ≤ 1 / 2) :
    Real.exp (-2 * ∑ ℓ ∈ B, y ℓ) ≤ ∏ ℓ ∈ B, (1 - y ℓ) := by
  rw [Finset.mul_sum, Real.exp_sum]
  exact Finset.prod_le_prod₀ (fun ℓ _ => (Real.exp_pos _).le)
    fun ℓ h => exp_neg_two_mul_le (hy ℓ h).1 (hy ℓ h).2

lemma prod_one_add_le_exp (B : Finset ℕ) (y : ℕ → ℝ) (hy : ∀ ℓ ∈ B, 0 ≤ y ℓ) {t : ℝ}
    (ht : 0 ≤ t) : ∏ ℓ ∈ B, (1 + t * y ℓ) ≤ Real.exp (t * ∑ ℓ ∈ B, y ℓ) := by
  rw [Finset.mul_sum, Real.exp_sum]
  refine Finset.prod_le_prod₀ (fun ℓ h => ?_) fun ℓ _ => ?_
  · have := hy ℓ h; positivity
  · have := Real.add_one_le_exp (t * y ℓ); linarith

/-- The relative size of the Bonferroni error term. -/
theorem E_div_prod_le (m : ℕ) (B : Finset ℕ) (y : ℕ → ℝ)
    (hy : ∀ ℓ ∈ B, 0 ≤ y ℓ ∧ y ℓ ≤ 1 / 2) {t : ℝ} (ht : 0 < t) :
    E m B y / ∏ ℓ ∈ B, (1 - y ℓ) ≤ Real.exp ((t + 2) * ∑ ℓ ∈ B, y ℓ) / t ^ m := by
  have hθ := exp_le_prod B y hy
  have hθpos : 0 < ∏ ℓ ∈ B, (1 - y ℓ) := (Real.exp_pos _).trans_le hθ
  have hE := E_le m B y (fun ℓ h => (hy ℓ h).1) ht
  have hP := prod_one_add_le_exp B y (fun ℓ h => (hy ℓ h).1) ht.le
  have htm : 0 < t ^ m := pow_pos ht m
  rw [div_le_div_iff₀ hθpos htm]
  have hE0 := E_nonneg m B y (fun ℓ h => (hy ℓ h).1)
  have hsplit : Real.exp ((t + 2) * ∑ ℓ ∈ B, y ℓ) =
      Real.exp (t * ∑ ℓ ∈ B, y ℓ) * Real.exp (2 * ∑ ℓ ∈ B, y ℓ) := by
    rw [← Real.exp_add]; ring_nf
  have hinv : Real.exp (2 * ∑ ℓ ∈ B, y ℓ) * Real.exp (-2 * ∑ ℓ ∈ B, y ℓ) = 1 := by
    rw [← Real.exp_add]; simp
  -- `E t^m ≤ ∏(1+ty) ≤ exp(tσ)` and `1 ≤ exp(2σ) θ`
  have h1 : E m B y * t ^ m ≤ Real.exp (t * ∑ ℓ ∈ B, y ℓ) := by
    rw [le_div_iff₀ htm] at hE; linarith
  have h2 : 1 ≤ Real.exp (2 * ∑ ℓ ∈ B, y ℓ) * ∏ ℓ ∈ B, (1 - y ℓ) := by
    have := mul_le_mul_of_nonneg_left hθ (Real.exp_pos (2 * ∑ ℓ ∈ B, y ℓ)).le
    linarith
  rw [hsplit]
  have hx : 0 ≤ Real.exp (t * ∑ ℓ ∈ B, y ℓ) := (Real.exp_pos _).le
  nlinarith [mul_le_mul_of_nonneg_left h2 hx]

end Shoup.Sieve
