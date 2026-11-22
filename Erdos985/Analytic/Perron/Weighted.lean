import Erdos985.Analytic.Perron.Kernel

/-!
# Perron's formula with the weight `(1 − n/N)`

`(1/2πi) ∫_{(c)} y^s / (s(s+1)) ds = max(0, 1 − 1/y)` for `y > 0`, `c > 0`, and the resulting
weighted Perron formula for an absolutely convergent Dirichlet series.
-/

open Complex MeasureTheory Set Filter

namespace Erdos985.Analytic.PerronKernel

theorem perron_kernel (y c : ℝ) (hy : 0 < y) (hc : 0 < c) :
    ∫ t : ℝ, (y : ℂ) ^ ((c : ℂ) + t * I) / (((c : ℂ) + t * I) * ((c : ℂ) + t * I + 1))
      = 2 * Real.pi * (if 1 ≤ y then 1 - 1 / y else 0) := by
  have h := perron_cesaro_aux y c hy hc
  have hpi : (2 * (Real.pi : ℂ)) ≠ 0 := by
    have := Real.pi_pos; exact mul_ne_zero two_ne_zero (ofReal_ne_zero.2 this.ne')
  have h' : (∫ t : ℝ, (y : ℂ) ^ ((c : ℂ) + t * I) / (((c : ℂ) + t * I) * ((c : ℂ) + t * I + 1)))
      = 2 * Real.pi * ((max 0 (1 - 1 / y) : ℝ) : ℂ) := by
    rw [← h, ← mul_assoc, mul_one_div_cancel hpi, one_mul]
  rw [h']
  congr 1
  split_ifs with h1
  · rw [max_eq_right (by rw [sub_nonneg, div_le_one hy]; exact h1)]
  · rw [max_eq_left (by
      rw [sub_nonpos, le_div_iff₀ hy]; linarith)]

/-- The kernel `y^s / (s(s+1))` on the line `re s = c`. -/
noncomputable def K (c y t : ℝ) : ℂ :=
  (y : ℂ) ^ ((c : ℂ) + t * I) / (((c : ℂ) + t * I) * ((c : ℂ) + t * I + 1))

lemma norm_K (c y t : ℝ) (hy : 0 < y) :
    ‖K c y t‖ = y ^ c * ‖1 / (((c : ℂ) + t * I) * ((c : ℂ) + t * I + 1))‖ := by
  unfold K
  rw [div_eq_mul_one_div, norm_mul, norm_cpow_eq_rpow_re_of_pos hy]
  simp

lemma integrable_K (c y : ℝ) (hc : 0 < c) (hy : 0 < y) : Integrable (K c y) := by
  have hcont : Continuous (K c y) := by
    unfold K
    have h0 : Continuous fun t : ℝ => (c : ℂ) + t * I :=
      continuous_const.add (continuous_ofReal.mul continuous_const)
    have h1 : Continuous fun t : ℝ => ((c : ℂ) + t * I) * ((c : ℂ) + t * I + 1) :=
      h0.mul (h0.add continuous_const)
    exact (h0.const_cpow (Or.inl (ofReal_ne_zero.2 hy.ne'))).div h1 (denom_ne_zero c hc)
  refine Integrable.mono' ((integrable_inv_denom c hc).norm.const_mul (y ^ c))
    hcont.aestronglyMeasurable (Eventually.of_forall fun t => ?_)
  rw [norm_K c y t hy]

lemma integral_norm_K (c y : ℝ) (hy : 0 < y) :
    ∫ t : ℝ, ‖K c y t‖ = y ^ c * ∫ t : ℝ, ‖1 / (((c : ℂ) + t * I) * ((c : ℂ) + t * I + 1))‖ := by
  simp_rw [norm_K c y _ hy]
  rw [integral_const_mul]

lemma term_mul_eq (a : ℕ → ℂ) (c t : ℝ) (N n : ℕ) (hN : 1 ≤ N) :
    LSeries.term a ((c : ℂ) + t * I) n * ((N : ℂ) ^ ((c : ℂ) + t * I)
        / (((c : ℂ) + t * I) * ((c : ℂ) + t * I + 1)))
      = if n = 0 then 0 else a n * K c ((N : ℝ) / n) t := by
  rw [LSeries.term_def]
  split_ifs with hn
  · simp
  · unfold K
    have hn0 : (0 : ℝ) < n := Nat.cast_pos.2 (Nat.pos_of_ne_zero hn)
    have hnc : (n : ℂ) ^ ((c : ℂ) + t * I) ≠ 0 := by
      rw [cpow_ne_zero_iff]; left; exact_mod_cast hn
    rw [ofReal_div, div_eq_mul_inv ((N : ℝ) : ℂ), ← ofReal_inv, mul_cpow_ofReal_nonneg
      (by positivity) (by positivity), ofReal_inv, inv_cpow_ofReal_nonneg hn0.le, ofReal_natCast,
      ofReal_natCast]
    field_simp

theorem perron_weighted (a : ℕ → ℂ) (c : ℝ) (hc : 0 < c)
    (ha : Summable fun n : ℕ => ‖a n‖ / (n : ℝ) ^ c) (N : ℕ) (hN : 1 ≤ N) :
    ∑ n ∈ Finset.Ioo 0 N, a n * (1 - (n : ℂ) / N)
      = (1 / (2 * Real.pi)) * ∫ t : ℝ, LSeries a ((c : ℂ) + t * I) * (N : ℂ) ^ ((c : ℂ) + t * I)
          / (((c : ℂ) + t * I) * ((c : ℂ) + t * I + 1)) := by
  set C := ∫ t : ℝ, ‖1 / (((c : ℂ) + t * I) * ((c : ℂ) + t * I + 1))‖ with hC
  have hC0 : 0 ≤ C := integral_nonneg fun _ => norm_nonneg _
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hpos : ∀ n : ℕ, n ≠ 0 → (0 : ℝ) < (N : ℝ) / n := fun n hn =>
    div_pos hN0 (Nat.cast_pos.2 (Nat.pos_of_ne_zero hn))
  let G : ℕ → ℝ → ℂ := fun n t => if n = 0 then 0 else a n * K c ((N : ℝ) / n) t
  have hG_int : ∀ n, Integrable (G n) := by
    intro n
    by_cases hn : n = 0
    · simp only [G, hn, ↓reduceIte]; exact integrable_zero _ _ _
    · simp only [G, hn, ↓reduceIte]; exact (integrable_K c _ hc (hpos n hn)).const_mul _
  have hG_norm : ∀ n, ∫ t, ‖G n t‖ = if n = 0 then 0 else ‖a n‖ * (((N : ℝ) / n) ^ c * C) := by
    intro n
    by_cases hn : n = 0
    · simp [G, hn]
    · simp only [G, hn, ↓reduceIte, norm_mul]
      rw [integral_const_mul, integral_norm_K c _ (hpos n hn)]
  have hsum : Summable fun n => ∫ t, ‖G n t‖ := by
    refine Summable.of_nonneg_of_le (fun n => integral_nonneg fun _ => norm_nonneg _)
      (fun n => ?_) (ha.mul_left ((N : ℝ) ^ c * C))
    rw [hG_norm]
    split_ifs with hn
    · have : 0 ≤ ‖a n‖ / (n : ℝ) ^ c := div_nonneg (norm_nonneg _) (by positivity)
      positivity
    · rw [Real.div_rpow hN0.le (Nat.cast_nonneg n)]
      apply le_of_eq
      ring
  have hfun : (fun t : ℝ => LSeries a ((c : ℂ) + t * I) * (N : ℂ) ^ ((c : ℂ) + t * I)
        / (((c : ℂ) + t * I) * ((c : ℂ) + t * I + 1))) = fun t => ∑' n, G n t := by
    funext t
    rw [mul_div_assoc, LSeries, ← tsum_mul_right]
    congr 1
    funext n
    exact term_mul_eq a c t N n hN
  have hGint : ∀ n, ∫ t, G n t = if n = 0 then 0 else
      a n * (2 * Real.pi * ((if 1 ≤ (N : ℝ) / n then 1 - 1 / ((N : ℝ) / n) else 0 : ℝ) : ℂ)) := by
    intro n
    by_cases hn : n = 0
    · simp [G, hn]
    · simp only [G, hn, ↓reduceIte]
      rw [integral_const_mul]
      unfold K
      rw [perron_kernel _ c (hpos n hn) hc]
  rw [hfun, ← integral_tsum_of_summable_integral_norm hG_int hsum]
  simp_rw [hGint]
  rw [tsum_eq_sum (s := Finset.Ioo 0 N), Finset.mul_sum]
  · refine Finset.sum_congr rfl fun n hn => ?_
    rw [Finset.mem_Ioo] at hn
    have hn0 : n ≠ 0 := by omega
    have hle : 1 ≤ (N : ℝ) / n := by
      rw [one_le_div (Nat.cast_pos.2 (by omega))]; exact_mod_cast hn.2.le
    simp only [hn0, hle, ↓reduceIte]
    have hpi : (Real.pi : ℂ) ≠ 0 := ofReal_ne_zero.2 Real.pi_pos.ne'
    have hnc : (n : ℂ) ≠ 0 := by exact_mod_cast hn0
    have hNc : (N : ℂ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
    push_cast
    field_simp
  · intro n hn
    rw [Finset.mem_Ioo] at hn
    by_cases hn0 : n = 0
    · simp [hn0]
    · simp only [hn0, ↓reduceIte]
      have hnN : N ≤ n := by omega
      rcases eq_or_lt_of_le hnN with h | h
      · subst h
        have hNc : ((N : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hn0
        simp [div_self (show (N : ℝ) ≠ 0 by exact_mod_cast hn0)]
      · have hlt : ¬ 1 ≤ (N : ℝ) / n := by
          rw [not_le, div_lt_one (Nat.cast_pos.2 (by omega))]; exact_mod_cast h
        simp [hlt]

end Erdos985.Analytic.PerronKernel
