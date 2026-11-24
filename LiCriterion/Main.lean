import LiCriterion.Zeros

/-!
# Li's criterion, forward direction: RH ⇒ `λₙ > 0` for every `n ≥ 1`

Under RH every `ρ ∈ nontrivialPosZeros` has `Re ρ = 1/2`, so `w = 1 - 1/ρ` lies on the unit
circle (`|ρ - 1| = |ρ|`). For `‖v‖ = 1`, `2 Re (1 - v) = ‖1 - v‖²`; with `v = wⁿ` each summand of
`lambda n` is `‖1 - wⁿ‖² ∈ [0, n² ‖ρ‖⁻²]` (`‖1 - wⁿ‖ ≤ n ‖1 - w‖ = n / ‖ρ‖`). The family is
therefore summable by `summable_inv_sq_nontrivialPosZeros`. A zero with `‖ρ‖ > n`
(`exists_nontrivialPosZeros_norm_gt`) has `‖1 - wⁿ‖ ≥ nδ - n²δ² > 0` for `δ = 1/‖ρ‖ < 1/n`, so
the sum is strictly positive.
-/

open Complex

namespace RiemannHypothesis

/-- `‖1 - wⁿ‖ ≤ n ‖1 - w‖` for `‖w‖ ≤ 1`. -/
lemma norm_one_sub_pow_le {w : ℂ} (hw : ‖w‖ ≤ 1) (n : ℕ) : ‖1 - w ^ n‖ ≤ n * ‖1 - w‖ := by
  induction n with
  | zero => simp
  | succ n ih =>
    have e : 1 - w ^ (n + 1) = (1 - w ^ n) + w ^ n * (1 - w) := by ring
    have h2 : ‖w ^ n * (1 - w)‖ ≤ 1 * ‖1 - w‖ := by
      rw [norm_mul, norm_pow]
      exact mul_le_mul_of_nonneg_right (pow_le_one₀ (norm_nonneg _) hw) (norm_nonneg _)
    rw [e]
    calc ‖(1 - w ^ n) + w ^ n * (1 - w)‖ ≤ ‖1 - w ^ n‖ + ‖w ^ n * (1 - w)‖ := norm_add_le _ _
      _ ≤ n * ‖1 - w‖ + 1 * ‖1 - w‖ := add_le_add ih h2
      _ = ((n + 1 : ℕ) : ℝ) * ‖1 - w‖ := by push_cast; ring

/-- Second order: `‖1 - wⁿ - n (1 - w)‖ ≤ n² ‖1 - w‖²` for `‖w‖ ≤ 1`. -/
lemma norm_one_sub_pow_sub_le {w : ℂ} (hw : ‖w‖ ≤ 1) (n : ℕ) :
    ‖1 - w ^ n - n * (1 - w)‖ ≤ (n : ℝ) ^ 2 * ‖1 - w‖ ^ 2 := by
  induction n with
  | zero => simp
  | succ n ih =>
    have e : 1 - w ^ (n + 1) - ((n + 1 : ℕ) : ℂ) * (1 - w)
        = (1 - w ^ n - n * (1 - w)) + (1 - w) * (w ^ n - 1) := by push_cast; ring
    have h2 : ‖(1 - w) * (w ^ n - 1)‖ ≤ ‖1 - w‖ * (n * ‖1 - w‖) := by
      rw [norm_mul, norm_sub_rev (w ^ n)]
      exact mul_le_mul_of_nonneg_left (norm_one_sub_pow_le hw n) (norm_nonneg _)
    rw [e]
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have hδ : 0 ≤ ‖1 - w‖ ^ 2 := sq_nonneg _
    calc ‖(1 - w ^ n - n * (1 - w)) + (1 - w) * (w ^ n - 1)‖
        ≤ ‖1 - w ^ n - n * (1 - w)‖ + ‖(1 - w) * (w ^ n - 1)‖ := norm_add_le _ _
      _ ≤ (n : ℝ) ^ 2 * ‖1 - w‖ ^ 2 + ‖1 - w‖ * (n * ‖1 - w‖) := add_le_add ih h2
      _ ≤ ((n + 1 : ℕ) : ℝ) ^ 2 * ‖1 - w‖ ^ 2 := by
          push_cast; nlinarith [mul_nonneg hn hδ]

/-- On the unit circle, `2 Re (1 - v) = ‖1 - v‖²`. -/
lemma two_mul_re_one_sub_eq {v : ℂ} (hv : ‖v‖ = 1) : 2 * (1 - v).re = ‖1 - v‖ ^ 2 := by
  have h : v.re * v.re + v.im * v.im = 1 := by
    rw [← Complex.normSq_apply, ← Complex.sq_norm, hv, one_pow]
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp only [sub_re, one_re, sub_im, one_im]
  linear_combination (-1 : ℝ) * h

/-- On the critical line, `‖1 - 1/ρ‖ = 1`. -/
lemma norm_one_sub_inv_eq_one {ρ : ℂ} (hre : ρ.re = 1 / 2) : ‖1 - 1 / ρ‖ = 1 := by
  have hρ0 : ρ ≠ 0 := fun h => by rw [h] at hre; norm_num at hre
  have hn : ‖ρ - 1‖ = ‖ρ‖ := by
    rw [Complex.norm_def, Complex.norm_def, Complex.normSq_apply, Complex.normSq_apply]
    congr 1
    simp only [sub_re, one_re, sub_im, one_im, hre]
    ring
  rw [show 1 - 1 / ρ = (ρ - 1) / ρ by field_simp, norm_div, hn,
    div_self (norm_ne_zero_iff.mpr hρ0)]

/-- Every element of `nontrivialPosZeros` is a nontrivial zero in Mathlib's sense, so RH puts it
on the critical line. -/
lemma re_eq_half_of_RH (hRH : RiemannHypothesis) {ρ : ℂ} (hρ : ρ ∈ nontrivialPosZeros) :
    ρ.re = 1 / 2 := by
  obtain ⟨_, _, him, hζ⟩ := hρ
  refine hRH ρ hζ ?_ ?_
  · rintro ⟨k, rfl⟩
    simp at him
  · rintro rfl
    simp at him

/-- The summand of `lambda n`, under RH: `2 Re (1 - wⁿ) = ‖1 - wⁿ‖²` with `w = 1 - 1/ρ`. -/
lemma summand_eq_of_RH (hRH : RiemannHypothesis) (n : ℕ) (ρ : nontrivialPosZeros) :
    2 * (1 - (1 - 1 / ρ.1) ^ n).re = ‖1 - (1 - 1 / ρ.1) ^ n‖ ^ 2 :=
  two_mul_re_one_sub_eq (by rw [norm_pow, norm_one_sub_inv_eq_one (re_eq_half_of_RH hRH ρ.2),
    one_pow])

lemma norm_one_sub_one_sub_inv (ρ : ℂ) : ‖1 - (1 - 1 / ρ)‖ = ‖ρ‖⁻¹ := by
  rw [sub_sub_cancel, norm_div, norm_one, one_div]

/-- Under RH the summands of `lambda n` are summable. -/
theorem summable_lambda_summand_of_RH (hRH : RiemannHypothesis) (n : ℕ) :
    Summable fun ρ : nontrivialPosZeros => 2 * (1 - (1 - 1 / ρ.1) ^ n).re := by
  refine Summable.of_nonneg_of_le (fun ρ => ?_) (fun ρ => ?_)
    (summable_inv_sq_nontrivialPosZeros.mul_left ((n : ℝ) ^ 2))
  · rw [summand_eq_of_RH hRH]; positivity
  · rw [summand_eq_of_RH hRH, ← mul_pow, ← norm_one_sub_one_sub_inv]
    have hw : ‖1 - 1 / ρ.1‖ ≤ 1 := (norm_one_sub_inv_eq_one (re_eq_half_of_RH hRH ρ.2)).le
    exact pow_le_pow_left₀ (norm_nonneg _) (norm_one_sub_pow_le hw n) 2

/-- A zero with `‖ρ‖ > n ≥ 1` contributes a strictly positive summand. -/
lemma summand_pos_of_RH (hRH : RiemannHypothesis) {n : ℕ} (hn : 0 < n) (ρ : nontrivialPosZeros)
    (hρ : (n : ℝ) < ‖ρ.1‖) : 0 < 2 * (1 - (1 - 1 / ρ.1) ^ n).re := by
  rw [summand_eq_of_RH hRH]
  set w : ℂ := 1 - 1 / ρ.1
  have hw : ‖w‖ ≤ 1 := (norm_one_sub_inv_eq_one (re_eq_half_of_RH hRH ρ.2)).le
  set δ : ℝ := ‖1 - w‖
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hρpos : 0 < ‖ρ.1‖ := hnpos.trans hρ
  have hδ : δ = ‖ρ.1‖⁻¹ := norm_one_sub_one_sub_inv _
  have hδpos : 0 < δ := by rw [hδ]; positivity
  have hnδ : n * δ < 1 := by
    rw [hδ, ← div_eq_mul_inv, div_lt_one hρpos]; exact hρ
  have h2 := norm_one_sub_pow_sub_le hw n
  -- `n δ = ‖n (1 - w)‖ ≤ ‖1 - wⁿ‖ + ‖1 - wⁿ - n (1 - w)‖`
  have h3 : (n : ℝ) * δ ≤ ‖1 - w ^ n‖ + ‖1 - w ^ n - n * (1 - w)‖ := by
    have e : (n : ℂ) * (1 - w) = (1 - w ^ n) - (1 - w ^ n - n * (1 - w)) := by ring
    have := norm_sub_le (1 - w ^ n) (1 - w ^ n - n * (1 - w))
    rw [← e, norm_mul, Complex.norm_natCast] at this
    exact this
  have h4 : 0 < ‖1 - w ^ n‖ := by
    have : 0 < (n : ℝ) * δ * (1 - n * δ) := mul_pos (mul_pos hnpos hδpos) (by linarith)
    nlinarith
  positivity

/-- **Li's criterion, RH ⇒ positivity** (Li 1997; Bombieri–Lagarias 1999): under the Riemann
hypothesis, `lambda n > 0` for every `n > 0`. This is formal-conjectures' `li_criterion_rhs`
with RH as a hypothesis. -/
theorem li_criterion_rhs_of_RH (hRH : RiemannHypothesis) : LiCriterionRHS := by
  intro n hn
  obtain ⟨ρ, hρ, hR⟩ := exists_nontrivialPosZeros_norm_gt n
  exact (summable_lambda_summand_of_RH hRH n).tsum_pos
    (fun ρ => by rw [summand_eq_of_RH hRH]; positivity) ⟨ρ, hρ⟩
    (summand_pos_of_RH hRH hn ⟨ρ, hρ⟩ hR)

/-- The forward direction of formal-conjectures' `li_criterion`. -/
theorem li_criterion_forward : RiemannHypothesis → ∀ n > 0, 0 < lambda n :=
  fun hRH _ hn => li_criterion_rhs_of_RH hRH hn

end RiemannHypothesis
