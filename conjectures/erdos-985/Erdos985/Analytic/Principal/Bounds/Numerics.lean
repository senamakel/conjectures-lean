import Mathlib

/-!
# Numerical inputs: `γ < 0.5774`, `log π > 1.144`
-/

open Real Filter Topology

namespace Erdos985.Analytic.PrincipalAux

/-- `log (1 + 1/a) ≥ 2y + 2y³/3` with `y = 1/(2a+1)`, first two terms of the artanh series. -/
lemma log_one_add_inv_ge {a : ℝ} (ha : 0 < a) :
    2 * (1 / (2 * a + 1)) + 2 / 3 * (1 / (2 * a + 1)) ^ 3 ≤ log (1 + a⁻¹) := by
  have h := hasSum_log_one_add_inv ha
  have hle := sum_le_hasSum (Finset.range 2) (fun k _ => by positivity) h
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hle
  norm_num at hle
  simpa [one_div, inv_pow] using hle

lemma step_ineq {a : ℝ} (ha : 0 < a) :
    1 / (2 * a) + 1 / (2 * (a + 1)) + 1 / (8 * (a + 1) ^ 2) - 1 / (8 * a ^ 2)
      ≤ log (1 + a⁻¹) := by
  refine le_trans ?_ (log_one_add_inv_ge ha)
  rw [← sub_nonneg]
  have e : 2 * (1 / (2 * a + 1)) + 2 / 3 * (1 / (2 * a + 1)) ^ 3 -
      (1 / (2 * a) + 1 / (2 * (a + 1)) + 1 / (8 * (a + 1) ^ 2) - 1 / (8 * a ^ 2))
      = (4 * a ^ 2 + 2 * a + 1) * (4 * a ^ 2 + 6 * a + 3) /
        (24 * a ^ 2 * (a + 1) ^ 2 * (2 * a + 1) ^ 3) := by
    field_simp
    ring
  rw [e]
  positivity

/-- `H_n − log n − 1/(2n) + 1/(8n²)`, shifted to start at `n = 1`. -/
noncomputable def emSeqU (m : ℕ) : ℝ :=
  (harmonic (m + 1) : ℝ) - log ((m + 1 : ℕ) : ℝ) - (1 / 2) / ((m + 1 : ℕ) : ℝ)
    + (1 / 8) / ((m + 1 : ℕ) : ℝ) ^ 2

lemma emSeqU_anti : Antitone emSeqU := by
  refine antitone_nat_of_succ_le (fun m => ?_)
  have ha : (0 : ℝ) < (m + 1 : ℕ) := by positivity
  have key := step_ineq ha
  have hlog : log (((m + 1 + 1 : ℕ) : ℝ)) =
      log ((m + 1 : ℕ) : ℝ) + log (1 + ((m + 1 : ℕ) : ℝ)⁻¹) := by
    rw [← log_mul ha.ne' (by positivity)]
    congr 1
    field_simp
    push_cast
    ring
  simp only [emSeqU]
  rw [hlog, harmonic_succ (m + 1)]
  push_cast at key ⊢
  have : (1 : ℝ) / (2 * (m + 1)) + 1 / (2 * (m + 1 + 1)) + 1 / (8 * (m + 1 + 1) ^ 2)
      - 1 / (8 * (m + 1) ^ 2) =
      ((m : ℝ) + 1 + 1)⁻¹ + 1 / 2 / (m + 1) - 1 / 2 / (m + 1 + 1)
        + 1 / 8 / (m + 1 + 1) ^ 2 - 1 / 8 / (m + 1) ^ 2 := by
    field_simp; ring
  linarith

lemma tendsto_emSeqU : Tendsto emSeqU atTop (𝓝 eulerMascheroniConstant) := by
  have h1 : Tendsto (fun n : ℕ => (harmonic n : ℝ) - log n - (1 / 2) / n + (1 / 8) / (n : ℝ) ^ 2)
      atTop (𝓝 (eulerMascheroniConstant - 0 + 0)) := by
    refine (tendsto_harmonic_sub_log.sub (tendsto_const_div_atTop_nhds_zero_nat _)).add ?_
    have := (tendsto_const_div_atTop_nhds_zero_nat (1 / 8 : ℝ)).comp
      (tendsto_pow_atTop (α := ℕ) (n := 2) (by norm_num))
    refine this.congr (fun n => ?_)
    simp
  rw [sub_zero, add_zero] at h1
  exact (tendsto_add_atTop_iff_nat 1).mpr h1

lemma le_emSeqU (m : ℕ) : eulerMascheroniConstant ≤ emSeqU m :=
  emSeqU_anti.le_of_tendsto tendsto_emSeqU m

lemma eulerMascheroniConstant_lt' : eulerMascheroniConstant < 0.5774 := by
  refine lt_of_le_of_lt (le_emSeqU 15) ?_
  have hH : (harmonic 16 : ℝ) = 2436559 / 720720 := by
    norm_num [harmonic, Finset.sum_range_succ]
  have hl : log ((16 : ℕ) : ℝ) = 4 * log 2 := by
    rw [show ((16 : ℕ) : ℝ) = 2 ^ 4 by norm_num, log_pow]; norm_num
  simp only [emSeqU]
  norm_num only [Nat.reduceAdd] at hH hl ⊢
  rw [hH, hl]
  linarith [log_two_gt_d9]

lemma log_pi_gt' : (1.144 : ℝ) < Real.log Real.pi := by
  rw [Real.lt_log_iff_exp_lt Real.pi_pos]
  have h1 : Real.exp 1.144 = Real.exp 1 * Real.exp 0.144 := by
    rw [← Real.exp_add]; norm_num
  have h2 := Real.exp_bound' (x := 0.144) (by norm_num) (by norm_num) (n := 4) (by norm_num)
  simp [Finset.sum_range_succ, Nat.factorial] at h2
  rw [h1]
  have h3 := Real.exp_one_lt_d9
  have h4 := Real.pi_gt_d4
  have h5 : 0 < Real.exp 0.144 := Real.exp_pos _
  nlinarith

/-- `2 + γ − log 4π < 1/20`. -/
lemma two_add_gamma_sub_log_lt : 2 + eulerMascheroniConstant - Real.log (4 * Real.pi) < 1 / 20 := by
  rw [Real.log_mul (by norm_num) Real.pi_pos.ne', show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
  have := eulerMascheroniConstant_lt'
  have := log_pi_gt'
  have := log_two_gt_d9
  push_cast
  linarith

end Erdos985.Analytic.PrincipalAux
