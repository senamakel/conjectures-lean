import Robin.Compute.Checkpoint

/-!
# Whole chunks preserve the invariant; the direct check for small `n`
-/

namespace Robin.Compute

open RobinCompute Real Finset ArithmeticFunction
open scoped ArithmeticFunction.sigma

theorem run_valid (x0 : ℕ) (sp : Array ℕ) (Bend : ℕ) :
    ∀ fuel s, Valid x0 s → Valid x0 (run Gc sp Bend fuel s)
  | 0, s, h => by simpa [run] using h
  | fuel + 1, s, h => by
    unfold run
    split_ifs
    · apply run_valid x0 sp Bend fuel
      have h1 := segStep_valid x0 sp s h
      split_ifs
      · exact checkpoint_valid h1
      · exact h1
    · exact h

theorem runChunk_valid {x0 : ℕ} {s : St} (h : Valid x0 s) (Bend : ℕ) :
    Valid x0 (runChunk Gc s Bend) :=
  run_valid x0 _ Bend Bend s h

/-! ### `σ` by trial division -/

lemma sigmaNat_go (n : ℕ) : ∀ d acc, sigmaNat.go n d acc =
    acc + ∑ i ∈ range d, (if n % (i + 1) = 0 then i + 1 else 0)
  | 0, acc => by simp [sigmaNat.go]
  | d + 1, acc => by
    rw [sigmaNat.go, sigmaNat_go n d, Finset.sum_range_succ]
    split_ifs <;> omega

theorem sigmaNat_eq (n : ℕ) : sigmaNat n = σ 1 n := by
  rw [sigma_one_apply, sigmaNat, sigmaNat_go, zero_add, Nat.divisors, Finset.sum_filter]
  rw [Finset.sum_Ico_eq_sum_range, show n + 1 - 1 = n by omega]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [Nat.dvd_iff_mod_eq_zero, add_comm]

theorem robinAt_of_directOK {n : ℕ} (h : directOK n = true) : RobinAt n := by
  have hG : ((Gc : ℤ) : ℝ) ≤ D * Real.eulerMascheroniConstant := gammaLoOf_le (by norm_num)
  unfold directOK at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨hn, h1⟩, h2⟩, h3⟩ := h
  have hD := D_pos
  have hD0 : 0 < D := by unfold D; positivity
  set L1 := logLoNat n
  set L2 := logLoQ L1 D
  set L3 := logLoQ L2 D
  have hL1 : (L1 : ℝ) ≤ D * Real.log n := logLoNat_le (by omega)
  have hL2 : (L2 : ℝ) ≤ D * Real.log ((L1 : ℝ) / D) := logLoQ_le hD0 h1.le
  have hL3 : (L3 : ℝ) ≤ D * Real.log ((L2 : ℝ) / D) := logLoQ_le hD0 h2.le
  have h1' : (D : ℝ) < L1 := by exact_mod_cast h1
  have h2' : (D : ℝ) < L2 := by exact_mod_cast h2
  clear_value L1 L2 L3
  have hq1 : 1 < (L1 : ℝ) / D := by rw [lt_div_iff₀ hD]; linarith
  have hq2 : 1 < (L2 : ℝ) / D := by rw [lt_div_iff₀ hD]; linarith
  have hlogn : (L1 : ℝ) / D ≤ Real.log n := by rw [div_le_iff₀ hD]; linarith
  have hll : Real.log ((L1 : ℝ) / D) ≤ Real.log (Real.log n) := Real.log_le_log (by linarith) hlogn
  have hll' : (L2 : ℝ) / D ≤ Real.log (Real.log n) := by
    rw [div_le_iff₀ hD]
    calc (L2 : ℝ) ≤ D * Real.log ((L1 : ℝ) / D) := hL2
      _ ≤ D * Real.log (Real.log n) := mul_le_mul_of_nonneg_left hll hD.le
      _ = Real.log (Real.log n) * D := by ring
  have hlll : Real.log ((L2 : ℝ) / D) ≤ Real.log (Real.log (Real.log n)) :=
    Real.log_le_log (by linarith) hll'
  have hσ1 : 1 ≤ σ 1 n := by
    have : 0 < σ 1 n := by rw [sigma_pos_iff]; omega
    omega
  have hσ := le_logUpNat hσ1
  rw [sigmaNat_eq] at h3
  have h3' : ((logUpNat (σ 1 n) : ℤ) : ℝ) < (L1 : ℝ) + (Gc : ℝ) + L3 := by exact_mod_cast h3
  push_cast at h3'
  have key : Real.log (σ 1 n) < Real.log n + Real.eulerMascheroniConstant +
      Real.log (Real.log (Real.log n)) := by
    have h4 : (L3 : ℝ) ≤ D * Real.log (Real.log (Real.log n)) :=
      hL3.trans (mul_le_mul_of_nonneg_left hlll hD.le)
    have : (D : ℝ) * Real.log (σ 1 n) < D * (Real.log n + Real.eulerMascheroniConstant +
        Real.log (Real.log (Real.log n))) := by
      rw [mul_add, mul_add]; linarith
    exact lt_of_mul_lt_mul_left this hD.le
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hσ0 : (0 : ℝ) < σ 1 n := by exact_mod_cast (show 0 < σ 1 n by omega)
  have hl : 0 < Real.log (Real.log n) := by
    have : 1 < Real.log n := by linarith
    exact Real.log_pos this
  have := Real.exp_lt_exp.mpr key
  rw [Real.exp_log hσ0, Real.exp_add, Real.exp_add, Real.exp_log hn0, Real.exp_log hl] at this
  unfold RobinAt
  linarith

end Robin.Compute
