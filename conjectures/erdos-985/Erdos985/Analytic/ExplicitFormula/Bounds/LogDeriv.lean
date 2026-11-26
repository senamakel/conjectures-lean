import Erdos985.Analytic.ExplicitFormula.Basic

/-!
# `‖L'/L(2, χ)‖ ≤ Σ Λ(n)/n² ≤ 0.6`

With `S = Σ Λ(n)/n²`, `Z = Σ 1/n² = π²/6` and `D = Σ log n/n²`, the identity `Λ ⋆ 1 = log`
gives `S · Z = D`. We bound `D ≤ 0.962` by the exact partial sum up to `n = 6` and the
telescoping tail `log n/n² ≤ G(n−1) − G(n)` with `G(x) = (log x + 1)/x`.
-/

set_option linter.unusedSimpArgs false

open Real ArithmeticFunction

namespace Erdos985.Analytic.BoundsAux

lemma term_eq2 (f : ℕ → ℝ) (n : ℕ) :
    LSeries.term (fun n => (f n : ℂ)) 2 n = ((f n / (n : ℝ) ^ 2 : ℝ) : ℂ) := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  · rw [LSeries.term_of_ne_zero hn, Complex.cpow_ofNat]
    push_cast
    rfl

lemma lseries_eq2 (f : ℕ → ℝ) :
    LSeries (fun n => (f n : ℂ)) 2 = ((∑' n : ℕ, f n / (n : ℝ) ^ 2 : ℝ) : ℂ) := by
  rw [LSeries, Complex.ofReal_tsum]
  exact tsum_congr (term_eq2 f)

lemma summable_of_lseries2 (f : ℕ → ℝ) (h : LSeriesSummable (fun n => (f n : ℂ)) 2) :
    Summable fun n : ℕ => f n / (n : ℝ) ^ 2 := by
  have : LSeries.term (fun n => (f n : ℂ)) 2 =
      fun n => ((f n / (n : ℝ) ^ 2 : ℝ) : ℂ) := funext (term_eq2 f)
  rw [LSeriesSummable, this] at h
  exact Complex.summable_ofReal.mp h

lemma re2 : 1 < (2 : ℂ).re := by norm_num

lemma summable_Λ2 : Summable fun n : ℕ => (Λ n : ℝ) / (n : ℝ) ^ 2 :=
  summable_of_lseries2 _ (LSeriesSummable_vonMangoldt re2)

lemma summable_log2 : Summable fun n : ℕ => Real.log n / (n : ℝ) ^ 2 := by
  refine summable_of_lseries2 (fun n => Real.log n) ?_
  have := (LSeriesSummable_vonMangoldt re2).convolution (LSeriesSummable_one_iff.mpr re2)
  rw [convolution_vonMangoldt_const_one] at this
  convert this using 2 with n
  simp [Complex.natCast_log]

lemma mul_eq2 :
    (∑' n : ℕ, (Λ n : ℝ) / (n : ℝ) ^ 2) * (∑' n : ℕ, (1 : ℝ) / (n : ℝ) ^ 2) =
      ∑' n : ℕ, Real.log n / (n : ℝ) ^ 2 := by
  have h := LSeries_convolution' (LSeriesSummable_vonMangoldt re2)
    (LSeriesSummable_one_iff.mpr re2)
  rw [convolution_vonMangoldt_const_one] at h
  have e1 := lseries_eq2 (fun n => (Λ n : ℝ))
  have e2 := lseries_eq2 (fun _ => (1 : ℝ))
  have e3 := lseries_eq2 (fun n : ℕ => Real.log n)
  have h1 : (1 : ℕ → ℂ) = fun _ => ((1 : ℝ) : ℂ) := by ext; simp
  have h3 : (fun n : ℕ => Complex.log n) = fun n : ℕ => ((Real.log n : ℝ) : ℂ) := by
    ext n; simp [Complex.natCast_log]
  rw [h1, h3, e1, e2, e3] at h
  exact_mod_cast h.symm

lemma g2_anti {c y : ℝ} (hc : 2 ≤ c) (hcy : c ≤ y) :
    Real.log y / y ^ 2 ≤ Real.log c / c ^ 2 := by
  have hc0 : 0 < c := by linarith
  have hy0 : 0 < y := by linarith
  have hL : 2 / 3 ≤ Real.log c := by
    have := Real.log_le_log (by norm_num) hc
    linarith [Real.log_two_gt_d9]
  have hlog : Real.log y - Real.log c ≤ y / c - 1 := by
    rw [← Real.log_div hy0.ne' hc0.ne']
    exact Real.log_le_sub_one_of_pos (by positivity)
  have hlog' : (Real.log y - Real.log c) * c ≤ y - c := by
    have : y / c - 1 = (y - c) / c := by field_simp
    rw [this, le_div_iff₀ hc0] at hlog; exact hlog
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have h1 : 0 ≤ y - c := by linarith
  -- log y * c^2 ≤ log c * c^2 + (y - c) c ≤ log c * y^2
  have : (y - c) * c ≤ Real.log c * (y - c) * (y + c) := by
    have : c ≤ Real.log c * (y + c) := by nlinarith
    nlinarith
  nlinarith

noncomputable def G2 (x : ℝ) : ℝ := (Real.log x + 1) / x

lemma hasDerivAt_G2 {t : ℝ} (ht : 0 < t) :
    HasDerivAt G2 (-(Real.log t / t ^ 2)) t := by
  have h1 : HasDerivAt (fun x => Real.log x + 1) (t⁻¹) t :=
    (Real.hasDerivAt_log ht.ne').add_const 1
  have := h1.div (hasDerivAt_id' t) ht.ne'
  unfold G2
  convert this using 1
  field_simp
  ring

lemma d2_step {x : ℝ} (hx : 2 ≤ x) :
    Real.log (x + 1) / (x + 1) ^ 2 ≤ G2 x - G2 (x + 1) := by
  obtain ⟨c, hc, hcd⟩ := exists_hasDerivAt_eq_slope G2 (fun t => -(Real.log t / t ^ 2))
    (by linarith : x < x + 1)
    (fun t ht => (hasDerivAt_G2 (by linarith [ht.1])).continuousAt.continuousWithinAt)
    (fun t ht => hasDerivAt_G2 (by linarith [ht.1]))
  have : G2 x - G2 (x + 1) = Real.log c / c ^ 2 := by
    rw [show x + 1 - x = 1 by ring, div_one] at hcd
    linarith
  rw [this]
  exact g2_anti (by linarith [hc.1]) hc.2.le

lemma G2_nonneg {x : ℝ} (hx : 1 ≤ x) : 0 ≤ G2 x := by
  unfold G2
  have := Real.log_nonneg hx
  have : 0 < x := by linarith
  positivity

lemma d2_tail (K : ℕ) (hK : 3 ≤ K) :
    ∑' i : ℕ, Real.log ((i + K : ℕ) : ℝ) / (((i + K : ℕ) : ℝ)) ^ 2 ≤ G2 ((K : ℝ) - 1) := by
  have hK' : (3 : ℝ) ≤ K := by exact_mod_cast hK
  refine Real.tsum_le_of_sum_range_le (fun i => ?_) (fun M => ?_)
  · have : (1 : ℝ) ≤ ((i + K : ℕ) : ℝ) := by push_cast; linarith [(i.cast_nonneg : (0 : ℝ) ≤ i)]
    have := Real.log_nonneg this
    positivity
  · have htel := Finset.sum_range_sub' (fun i : ℕ => G2 ((K : ℝ) - 1 + i)) M
    simp only [Nat.cast_zero, add_zero] at htel
    have hG : 0 ≤ G2 ((K : ℝ) - 1 + M) :=
      G2_nonneg (by linarith [(M.cast_nonneg : (0 : ℝ) ≤ M)])
    refine le_trans (Finset.sum_le_sum (fun i _ => ?_)) (le_of_eq_of_le htel (by linarith))
    have hx : (2 : ℝ) ≤ (K : ℝ) - 1 + i := by linarith [(i.cast_nonneg : (0 : ℝ) ≤ i)]
    have := d2_step hx
    push_cast
    rw [show (K : ℝ) - 1 + ((i : ℝ) + 1) = (K : ℝ) - 1 + i + 1 by ring,
      show (i : ℝ) + K = (K : ℝ) - 1 + i + 1 by ring]
    exact this

lemma D2_le : ∑' n : ℕ, Real.log n / (n : ℝ) ^ 2 ≤ 0.962 := by
  obtain ⟨l2, l3, l5, -, -, -, -, -⟩ := ConstantsAux.log_primes_le
  have hD := (summable_log2.sum_add_tsum_nat_add 7).symm
  have hdt := d2_tail 7 (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hD
  norm_num at hD hdt
  unfold G2 at hdt
  have e4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2^2 by norm_num]; simp [Real.log_mul, Real.log_pow]
  have e6 : Real.log 6 = Real.log 2 + Real.log 3 := by
    rw [show (6 : ℝ) = 2 * 3 by norm_num]; simp [Real.log_mul, Real.log_pow]
  rw [hD]
  norm_num [e4, e6] at hdt ⊢
  linarith

lemma S2_le : ∑' n : ℕ, (Λ n : ℝ) / (n : ℝ) ^ 2 ≤ 0.6 := by
  have hmul := mul_eq2
  have hZ : ∑' n : ℕ, (1 : ℝ) / (n : ℝ) ^ 2 = π ^ 2 / 6 := hasSum_zeta_two.tsum_eq
  have hD := D2_le
  have hS : 0 ≤ ∑' n : ℕ, (Λ n : ℝ) / (n : ℝ) ^ 2 :=
    tsum_nonneg fun n => div_nonneg vonMangoldt_nonneg (by positivity)
  rw [hZ] at hmul
  have hpi : (1.643 : ℝ) ≤ π ^ 2 / 6 := by
    nlinarith [Real.pi_gt_d2, mul_self_le_mul_self (by norm_num : (0:ℝ) ≤ 3.14) Real.pi_gt_d2.le]
  set S := ∑' n : ℕ, (Λ n : ℝ) / (n : ℝ) ^ 2
  by_contra h
  have h' := (not_le.mp h).le
  nlinarith [mul_le_mul h' hpi (by norm_num) hS]

end Erdos985.Analytic.BoundsAux

namespace Erdos985.Analytic

open Complex BoundsAux

variable {N : ℕ} [NeZero N]

theorem norm_logDeriv_LFunction_two_le' (χ : DirichletCharacter ℂ N) :
    ‖deriv (DirichletCharacter.LFunction χ) 2 / DirichletCharacter.LFunction χ 2‖ ≤ 0.6 := by
  have hev : DirichletCharacter.LFunction χ =ᶠ[nhds 2] LSeries (fun n => χ n) := by
    have ho : IsOpen {s : ℂ | 1 < s.re} := isOpen_lt continuous_const Complex.continuous_re
    filter_upwards [ho.mem_nhds (show (2 : ℂ) ∈ {s : ℂ | 1 < s.re} by norm_num)] with s hs
    exact DirichletCharacter.LFunction_eq_LSeries χ hs
  rw [hev.deriv_eq, hev.eq_of_nhds]
  have key := DirichletCharacter.LSeries_twist_vonMangoldt_eq χ re2
  rw [show deriv (LSeries fun n => χ n) 2 / LSeries (fun n => χ n) 2
      = -(-deriv (LSeries fun n => χ n) 2 / LSeries (fun n => χ n) 2) by ring, ← key, norm_neg]
  refine le_trans ?_ S2_le
  have hsum := DirichletCharacter.LSeriesSummable_twist_vonMangoldt χ re2
  rw [LSeries]
  refine (norm_tsum_le_tsum_norm hsum.norm).trans ?_
  refine Summable.tsum_le_tsum (fun n => ?_) hsum.norm summable_Λ2
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  rw [LSeries.term_of_ne_zero hn, Complex.cpow_ofNat, norm_div, Pi.mul_apply, norm_mul, norm_pow,
    Complex.norm_natCast]
  rw [show ‖((Λ n : ℝ) : ℂ)‖ = Λ n from by
    rw [Complex.norm_real, Real.norm_of_nonneg vonMangoldt_nonneg]]
  gcongr
  calc ‖χ n‖ * Λ n ≤ 1 * Λ n :=
        mul_le_mul_of_nonneg_right (DirichletCharacter.norm_le_one χ n) vonMangoldt_nonneg
    _ = Λ n := one_mul _

end Erdos985.Analytic
