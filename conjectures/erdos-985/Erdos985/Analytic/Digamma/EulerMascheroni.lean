import Mathlib

open Real Filter Topology

namespace Erdos985.Analytic.DigammaAux

/-- `log (1 + 1/n) ≤ (1/n + 1/(n+1))/2` (trapezoid bound for the convex function `1/x`). -/
lemma log_one_add_inv_le {a : ℝ} (ha : 0 < a) :
    log (1 + a⁻¹) ≤ 1 / (2 * a) + 1 / (2 * (a + 1)) := by
  set y : ℝ := 1 / (2 * a + 1) with hy
  have hy0 : 0 < y := by positivity
  have hy1 : y < 1 := by rw [hy, div_lt_one (by linarith)]; linarith
  have hy2 : y ^ 2 < 1 := by nlinarith
  have hg : HasSum (fun k : ℕ => 2 * y * (y ^ 2) ^ k) (2 * y * (1 - y ^ 2)⁻¹) :=
    (hasSum_geometric_of_lt_one (by positivity) hy2).mul_left (2 * y)
  have hle := hasSum_le (fun k : ℕ => ?_) (hasSum_log_one_add_inv ha) hg
  · refine hle.trans (le_of_eq ?_)
    have h2a : (2 * a + 1) ≠ 0 := by positivity
    have e1 : 1 - y ^ 2 = 4 * a * (a + 1) / (2 * a + 1) ^ 2 := by
      rw [hy]; field_simp; ring
    rw [e1, hy]
    field_simp
    ring
  · rw [← hy, pow_succ, ← pow_mul]
    have h1 : (1 : ℝ) / (2 * k + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]; linarith [k.cast_nonneg (α := ℝ)]
    have h2 : 0 ≤ y ^ (2 * k) * y := by positivity
    nlinarith

/-- The sequence `H_n - log n - 1/(2n)`, shifted to start at `n = 1`. -/
noncomputable def emSeq (m : ℕ) : ℝ :=
  (harmonic (m + 1) : ℝ) - log ((m + 1 : ℕ) : ℝ) - (1 / 2) / ((m + 1 : ℕ) : ℝ)

lemma emSeq_mono : Monotone emSeq := by
  refine monotone_nat_of_le_succ (fun m => ?_)
  have ha : (0 : ℝ) < (m + 1 : ℕ) := by positivity
  have key := log_one_add_inv_le ha
  have hlog : log (((m + 1 + 1 : ℕ) : ℝ)) = log ((m + 1 : ℕ) : ℝ) + log (1 + ((m + 1 : ℕ) : ℝ)⁻¹) := by
    rw [← log_mul ha.ne' (by positivity)]
    congr 1
    field_simp
    push_cast
    ring
  simp only [emSeq]
  rw [hlog, harmonic_succ (m + 1)]
  push_cast at key ⊢
  have : (1 : ℝ) / (2 * (m + 1)) + 1 / (2 * (m + 1 + 1)) = 
      ((m : ℝ) + 1 + 1)⁻¹ + 1 / 2 / (m + 1) - 1 / 2 / (m + 1 + 1) := by
    field_simp; ring
  linarith

lemma tendsto_emSeq : Tendsto emSeq atTop (𝓝 eulerMascheroniConstant) := by
  have h1 : Tendsto (fun n : ℕ => (harmonic n : ℝ) - log n - (1 / 2) / n) atTop
      (𝓝 (eulerMascheroniConstant - 0)) :=
    tendsto_harmonic_sub_log.sub (tendsto_const_div_atTop_nhds_zero_nat _)
  rw [sub_zero] at h1
  exact (tendsto_add_atTop_iff_nat 1).mpr h1

lemma emSeq_le (m : ℕ) : emSeq m ≤ eulerMascheroniConstant :=
  emSeq_mono.ge_of_tendsto tendsto_emSeq m

lemma eulerMascheroniConstant_gt : (0.57688 : ℝ) < eulerMascheroniConstant := by
  refine lt_of_lt_of_le ?_ (emSeq_le 15)
  have hH : (harmonic 16 : ℝ) = 2436559 / 720720 := by
    norm_num [harmonic, Finset.sum_range_succ]
  have hl : log ((16 : ℕ) : ℝ) = 4 * log 2 := by
    rw [show ((16 : ℕ) : ℝ) = 2 ^ 4 by norm_num, log_pow]; norm_num
  simp only [emSeq]
  norm_num only [Nat.reduceAdd] at hH hl ⊢
  rw [hH, hl]
  linarith [log_two_lt_d9]

end Erdos985.Analytic.DigammaAux
