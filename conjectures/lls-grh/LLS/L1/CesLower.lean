import LLS.L1.Defs
import LLS.Analytic.ShiftFormula

/-! # LLS Lemma 2.3, the other direction, and `D(1) = G(1) + L'/L(1)`

The lower bound reuses the exact identity behind `LLS.re_cesShift_le`
(`ShiftAux.shift_identity`, `ShiftAux.zeroPart_eq`). For the gamma part, each residue term
`tau x m` (`m ≥ 2`) is at least `1/(m+2) − 1/m`, and these telescope to `−1/3` (even
characters, `m = 3, 5, …`) or `−1/2` (odd characters, `m = 2, 4, …`).
-/

namespace LLS

open Complex ArithmeticFunction Erdos985 Erdos985.Analytic Erdos985.Analytic.BoundsAux ShiftAux

variable {N : ℕ} [NeZero N]

lemma tau_ge_tele (x : ℝ) (hx : 1 ≤ x) (m : ℕ) (hm : 2 ≤ m) :
    1 / ((m : ℝ) + 2) - 1 / m ≤ tau x m := by
  have hm0 : m ≠ 0 := by omega
  have hm1 : m ≠ 1 := by omega
  simp only [tau, hm0, hm1, ite_false]
  set y := 1 / x with hy
  have hy0 : 0 < y := by positivity
  have hy1 : y ≤ 1 := by rw [hy, div_le_one (by linarith)]; exact hx
  have hmR : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have hpow : y ^ m ≤ y := pow_le_of_le_one hy0.le hy1 hm0
  have hpow0 : 0 ≤ y ^ m := by positivity
  have h1 : (m : ℝ) - 1 ≠ 0 := by intro h; linarith
  have h2 : (m : ℝ) ≠ 0 := by intro h; linarith
  have h3 : (2 : ℝ) + m ≠ 0 := by intro h; linarith
  have e : (1 - y) / (2 + (m : ℝ)) - (y ^ m / ((m : ℝ) * ((m : ℝ) - 1)) + 1 / m - y / ((m : ℝ) - 1))
      - (1 / ((m : ℝ) + 2) - 1 / m)
      = (y * (2 * (m : ℝ) - 2) + (y - y ^ m) * ((m : ℝ) + 2))
        / ((m : ℝ) * ((m : ℝ) - 1) * ((m : ℝ) + 2)) := by
    field_simp
    ring
  rw [← sub_nonneg, e]
  apply div_nonneg
  · have : 0 ≤ (y - y ^ m) * ((m : ℝ) + 2) := mul_nonneg (by linarith) (by linarith)
    have : 0 ≤ y * (2 * (m : ℝ) - 2) := mul_nonneg hy0.le (by linarith)
    linarith
  · have : 0 ≤ (m : ℝ) - 1 := by linarith
    positivity

/-- Telescoping: `Σ_k (1/(2k + a) − 1/(2k + a + 2)) = 1/a` for `a > 0`. -/
lemma hasSum_tele (a : ℝ) (ha : 0 < a) :
    HasSum (fun k : ℕ => 1 / (2 * (k : ℝ) + a) - 1 / (2 * (k : ℝ) + a + 2)) (1 / a) := by
  have hnn : ∀ k : ℕ, 0 ≤ 1 / (2 * (k : ℝ) + a) - 1 / (2 * (k : ℝ) + a + 2) := by
    intro k
    have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    rw [sub_nonneg]
    exact one_div_le_one_div_of_le (by positivity) (by linarith)
  rw [hasSum_iff_tendsto_nat_of_nonneg hnn]
  have hps : ∀ n : ℕ, ∑ i ∈ Finset.range n, (1 / (2 * (i : ℝ) + a) - 1 / (2 * (i : ℝ) + a + 2))
      = 1 / a - 1 / (2 * (n : ℝ) + a) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      push_cast
      ring_nf
  simp_rw [hps]
  have h : Filter.Tendsto (fun n : ℕ => 1 / (2 * (n : ℝ) + a)) Filter.atTop (nhds 0) := by
    have h2 : Filter.Tendsto (fun n : ℕ => 2 * (n : ℝ) + a) Filter.atTop Filter.atTop :=
      Filter.tendsto_atTop_add_const_right _ _
        (tendsto_natCast_atTop_atTop.const_mul_atTop (by norm_num))
    have := h2.inv_tendsto_atTop
    simp only [one_div]
    exact this
  simpa using h.const_sub (1 / a)

/-- The gamma part plus `(1 − 1/x) G(3)` is at least `EshiftLo x`. -/
theorem re_gamma_shift_ge (χ : DirichletCharacter ℂ N) (x : ℕ) (hx : 1 ≤ x) :
    EshiftLo x ≤ (gammaPartS χ x + (1 - 1 / (x : ℂ)) * gammaLogDeriv χ 3).re := by
  have hx1 : (1 : ℝ) ≤ x := by exact_mod_cast hx
  have hx0 : (0 : ℝ) < x := by linarith
  set y : ℝ := 1 / x with hy
  have hy0 : 0 < y := by positivity
  have hy1 : y ≤ 1 := by rw [hy, div_le_one hx0]; exact hx1
  have hL : 0 ≤ Real.log x := Real.log_nonneg hx1
  have hfac : (1 - 1 / (x : ℂ)) = ((1 - y : ℝ) : ℂ) := by rw [hy]; push_cast; ring
  rw [gammaPartS_eq χ x hx, hfac, ← Complex.ofReal_tsum, add_re, ofReal_re, re_ofReal_mul,
    ShiftAux.re_gammaLogDeriv_three]
  have hl2 := Real.log_two_gt_d9
  have hγ := Erdos985.Analytic.DigammaAux.eulerMascheroniConstant_gt
  have hpi : 0 < Real.log Real.pi := Real.log_pos (by linarith [Real.pi_gt_three])
  unfold EshiftLo
  rw [← hy]
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp (parity_le_one χ) with h | h
  · -- even: `Σ_k tau(2k+1) = tau 1 + Σ_k tau(2k+3) ≥ tau 1 − 1/3`
    rw [h]
    simp only [↓reduceIte, add_zero]
    have hS := (tsum_tau_bound x hx1 1 le_rfl).1
    have hS' : Summable (fun k : ℕ => tau x (2 * k + 1)) := by simpa using hS
    rw [hS'.tsum_eq_zero_add]
    have hg : Summable (fun k : ℕ => tau x (2 * (k + 1) + 1)) :=
      (summable_nat_add_iff (f := fun k : ℕ => tau x (2 * k + 1)) 1).mpr hS'
    have ht := (hasSum_tele 3 (by norm_num)).neg
    have hge : -(1 / 3 : ℝ) ≤ ∑' k : ℕ, tau x (2 * (k + 1) + 1) := by
      rw [← ht.tsum_eq]
      refine Summable.tsum_le_tsum (fun k => ?_) ht.summable hg
      have := tau_ge_tele x hx1 (2 * (k + 1) + 1) (by omega)
      push_cast at this ⊢
      have e1 : (2 * ((k : ℝ) + 1) + 1 : ℝ) = 2 * k + 3 := by ring
      rw [e1] at this
      have e2 : (2 * (k : ℝ) + 3 + 2) = 2 * k + 3 + 2 := rfl
      linarith
    have ht1 : tau x (2 * 0 + 1) = (1 - y) / 3 - (1 - y - y * Real.log x) := by
      simp [tau, hy]
    rw [ht1]
    nlinarith [mul_nonneg hy0.le hL]
  · -- odd: `Σ_k tau(2k+2) ≥ −1/2`
    rw [h]
    simp only [one_ne_zero, ↓reduceIte]
    have hS := (tsum_tau_bound x hx1 0 (by norm_num)).1
    have hS' : Summable (fun k : ℕ => tau x (2 * k)) := by simpa using hS
    have hg : Summable (fun k : ℕ => tau x (2 * (k + 1))) :=
      (summable_nat_add_iff (f := fun k : ℕ => tau x (2 * k)) 1).mpr hS'
    have he : (fun k : ℕ => tau x (2 * k + 1 + 1)) = fun k : ℕ => tau x (2 * (k + 1)) := by
      funext k; congr 1
    rw [he]
    have ht := (hasSum_tele 2 (by norm_num)).neg
    have hge : -(1 / 2 : ℝ) ≤ ∑' k : ℕ, tau x (2 * (k + 1)) := by
      rw [← ht.tsum_eq]
      refine Summable.tsum_le_tsum (fun k => ?_) ht.summable hg
      have := tau_ge_tele x hx1 (2 * (k + 1)) (by omega)
      push_cast at this ⊢
      have e1 : (2 * ((k : ℝ) + 1) : ℝ) = 2 * k + 2 := by ring
      rw [e1] at this
      linarith
    nlinarith

/-- LLS Lemma 2.3 (lower bound for the real part). -/
theorem re_cesShift_ge (hGRH : DirichletLNonvanishingRightOfHalf) {χ : DirichletCharacter ℂ N}
    (hprim : χ.IsPrimitive) (hχ : χ ≠ 1) (x : ℕ) (hx : 2 ≤ x) :
    -(D χ 1).re - (Real.log N + (D χ⁻¹ 1).re) / x - Z2 χ / √(x : ℝ) + EshiftLo x
      ≤ (cesShift χ x).re := by
  have hx1 : 1 ≤ x := by omega
  obtain ⟨Z, hZ, hZeq⟩ := zeroPart_eq hGRH hprim hχ x hx1
  have hid := shift_identity hGRH hprim hχ x hx1
  have hc3 := logDeriv_LFunction_eq hχ (s := 3) (by norm_num)
  have hχi : χ⁻¹ ≠ 1 := by simpa using hχ
  have hFE := ZeroSumAux.logDeriv_functional_equation hprim hχ (s := 1)
    (DirichletCharacter.completedLFunction_ne_zero_of_one_le_re χ⁻¹ (Or.inl hχi) (by norm_num))
  rw [sub_self] at hFE
  have hD0 : D χ 0 = -((Real.log N : ℂ) + D χ⁻¹ 1) := by
    unfold D; rw [← hFE]; ring
  have hmain : cesShift χ x = -D χ 1 + D χ 0 / x - Z
      + (gammaPartS χ x + (1 - 1 / (x : ℂ)) * gammaLogDeriv χ 3) := by
    rw [hid, hZeq, hc3]
    unfold D
    ring
  have hG := re_gamma_shift_ge χ x hx1
  have hre0 : (D χ 0 / (x : ℂ)).re = -(Real.log N + (D χ⁻¹ 1).re) / x := by
    rw [Complex.div_natCast_re, hD0, neg_re, add_re, ofReal_re]
  have hZre : Z.re ≤ Z2 χ / √(x : ℝ) := (Complex.re_le_norm Z).trans hZ
  have hre : (cesShift χ x).re = -(D χ 1).re + (D χ 0 / (x : ℂ)).re - Z.re
      + (gammaPartS χ x + (1 - 1 / (x : ℂ)) * gammaLogDeriv χ 3).re := by
    rw [hmain, add_re, sub_re, add_re, neg_re]
  rw [hre, hre0, neg_div]
  linarith

/-- `Λ'/Λ(1) = G(1) + L'/L(1)` at the edge of the half-plane of convergence. -/
theorem D_one_eq {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1) :
    D χ 1 = gammaLogDeriv χ 1
      + deriv (DirichletCharacter.LFunction χ) 1 / DirichletCharacter.LFunction χ 1 := by
  have hs0 : 0 < (1 : ℂ).re := by norm_num
  have hL : DirichletCharacter.LFunction χ 1 ≠ 0 :=
    DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inl hχ) (by norm_num)
  have hγ := StepAAux.gammaFactor_ne_zero χ hs0
  have hev : DirichletCharacter.completedLFunction χ =ᶠ[nhds 1]
      fun w => DirichletCharacter.gammaFactor χ w * DirichletCharacter.LFunction χ w := by
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds
      (show (1 : ℂ) ∈ {w : ℂ | 0 < w.re} from hs0)] with w hw
    rw [DirichletCharacter.LFunction_eq_completed_div_gammaFactor χ w
      (Or.inl fun h => by rw [h] at hw; simp at hw),
      mul_div_cancel₀ _ (StepAAux.gammaFactor_ne_zero χ hw)]
  have hd : HasDerivAt (fun w => DirichletCharacter.gammaFactor χ w
      * DirichletCharacter.LFunction χ w) _ 1 :=
    (StepAAux.hasDerivAt_gammaFactor χ hs0).mul
      (DirichletCharacter.differentiableAt_LFunction χ 1 (Or.inr hχ)).hasDerivAt
  unfold D
  rw [hev.deriv_eq, hd.deriv, hev.eq_of_nhds]
  field_simp

end LLS
