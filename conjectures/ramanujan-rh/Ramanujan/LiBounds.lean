import Ramanujan.LiExpansion

/-!
# Two-sided bounds for `li y`, `y ≥ e¹⁵`

With `A ℓ = Σ_{k<8} k!/ℓ^{k+1}` (the first eight terms of the asymptotic series) and
`ℓ = log y`:

* `li_upper`: `li y ≤ y · A ℓ + 2e¹⁵ + 100800 · y/ℓ⁹`,
* `li_lower`: `y · A ℓ − e¹⁵ ≤ li y`.

Both come from the eight-fold integration by parts of `LiExpansion` with base point `a = e¹⁵`:
the remainder `8! · I 9 a y` lies in `[0, 8! · (5/2) · y/ℓ⁹]` since `9/log a = 3/5`, and
`0 ≤ li a ≤ 2a`, `a · A 15 ≤ a`.
-/

namespace Ramanujan

open Real

/-- `A ℓ = Σ_{k<8} k! / ℓ^{k+1}`. -/
noncomputable def A (ℓ : ℝ) : ℝ := ∑ k ∈ Finset.range 8, (k.factorial : ℝ) / ℓ ^ (k + 1)

lemma sum_split (y a ly la : ℝ) :
    (∑ k ∈ Finset.range 8, (k.factorial : ℝ) * (y / ly ^ (k + 1) - a / la ^ (k + 1))) =
      y * A ly - a * A la := by
  unfold A
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  ring

lemma A_nonneg {ℓ : ℝ} (h : 0 < ℓ) : 0 ≤ A ℓ :=
  Finset.sum_nonneg fun k _ => by positivity

lemma A_fifteen_le : A 15 ≤ 1 := by
  unfold A
  simp [Finset.sum_range_succ, Nat.factorial]
  norm_num

lemma A_eq {u : ℝ} (hu : u ≠ 0) :
    A u = (u ^ 8 + u ^ 7 + 2 * u ^ 6 + 6 * u ^ 5 + 24 * u ^ 4 + 120 * u ^ 3 + 720 * u ^ 2 +
      5040 * u) / u ^ 9 := by
  unfold A
  simp [Finset.sum_range_succ, Nat.factorial]
  field_simp

lemma two_le_exp_fifteen : 2 ≤ Real.exp 15 := by
  have := Real.add_one_le_exp 15
  linarith

lemma setup_a : 1 < Real.exp 15 ∧ Real.log (Real.exp 15) = 15 :=
  ⟨by linarith [two_le_exp_fifteen], Real.log_exp 15⟩

/-- `li y ≤ y · A(log y) + 2e¹⁵ + 100800 · y / log⁹ y` for `y ≥ e¹⁵`. -/
theorem li_upper {y : ℝ} (hy : Real.exp 15 ≤ y) :
    Real.logIntegral y ≤
      y * A (Real.log y) + 2 * Real.exp 15 + 100800 * (y / Real.log y ^ 9) := by
  obtain ⟨ha1, hla⟩ := setup_a
  have e1 := logIntegral_eq (Real.exp 15) y two_le_exp_fifteen hy
  have e2 := I_one_expansion 8 ha1 hy
  rw [sum_split, hla] at e2
  have hI := I_le 9 ha1 hy
  rw [hla] at hI
  have hA := A_nonneg (by norm_num : (0 : ℝ) < 15)
  have hli := (logIntegral_bounds two_le_exp_fifteen).2
  have hpos : 0 ≤ Real.exp 15 * A 15 := mul_nonneg (Real.exp_pos 15).le hA
  have h8 : ((Nat.factorial 8 : ℕ) : ℝ) = 40320 := by norm_num [Nat.factorial]
  rw [h8] at e2
  norm_num at hI
  nlinarith

/-- `y · A(log y) − e¹⁵ ≤ li y` for `y ≥ e¹⁵`. -/
theorem li_lower {y : ℝ} (hy : Real.exp 15 ≤ y) :
    y * A (Real.log y) - Real.exp 15 ≤ Real.logIntegral y := by
  obtain ⟨ha1, hla⟩ := setup_a
  have e1 := logIntegral_eq (Real.exp 15) y two_le_exp_fifteen hy
  have e2 := I_one_expansion 8 ha1 hy
  rw [sum_split, hla] at e2
  have hI := I_nonneg 9 ha1 hy
  have hli := (logIntegral_bounds two_le_exp_fifteen).1
  have hA : Real.exp 15 * A 15 ≤ Real.exp 15 :=
    mul_le_of_le_one_right (Real.exp_pos 15).le A_fifteen_le
  have h8 : ((Nat.factorial 8 : ℕ) : ℝ) = 40320 := by norm_num [Nat.factorial]
  rw [h8] at e2
  nlinarith

end Ramanujan
