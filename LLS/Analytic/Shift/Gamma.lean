import LLS.Defs

/-!
# The gamma-factor term of the shifted Cesàro formula

On `Re s = 2`, `G(s+1) − G(3) = Σ_k (1/(2+m) − 1/(s+m))` with `m = 2k + 𝔞 + 1`, so integrating
against `x^s/(s(s+1))` gives `Σ_k tau x (2k + 𝔞 + 1)` (erdos-985's `tau`, the residue sum of the
digamma pole at `−m`). Together with `(1 − 1/x) G(3)` this is at most `Eshift x`.
-/

namespace LLS.ShiftAux

open Complex MeasureTheory Erdos985.Analytic Erdos985.Analytic.BoundsAux

variable {N : ℕ}

/-- The gamma part of the shifted Cesàro formula. -/
noncomputable def gammaPartS [NeZero N] (χ : DirichletCharacter ℂ N) (x : ℕ) : ℂ :=
  (1 / (2 * Real.pi) : ℂ) * ∫ t : ℝ,
    (gammaLogDeriv χ ((2 : ℂ) + t * I + 1) - gammaLogDeriv χ 3) * (x : ℂ) ^ ((2 : ℂ) + t * I)
      / (((2 : ℂ) + t * I) * ((2 : ℂ) + t * I + 1))

lemma hasSum_gammaLogDeriv_shift (χ : DirichletCharacter ℂ N) {s : ℂ} (hs : 1 < s.re) :
    HasSum (fun k : ℕ => 1 / (2 + ((2 * k + parity χ + 1 : ℕ) : ℂ))
        - 1 / (s + ((2 * k + parity χ + 1 : ℕ) : ℂ)))
      (gammaLogDeriv χ (s + 1) - gammaLogDeriv χ 3) := by
  have h1 := hasSum_gammaLogDeriv χ (s := s + 1) (by simp; linarith)
  have h3 := hasSum_gammaLogDeriv χ (s := 3) (by norm_num)
  convert h1.sub h3 using 1
  · funext k
    push_cast
    ring_nf
  · ring

lemma gamma_integrand_eq (χ : DirichletCharacter ℂ N) (x : ℕ) (t : ℝ) :
    (gammaLogDeriv χ ((2 : ℂ) + t * I + 1) - gammaLogDeriv χ 3) * (x : ℂ) ^ ((2 : ℂ) + t * I)
      / (((2 : ℂ) + t * I) * ((2 : ℂ) + t * I + 1)) =
      ∑' k : ℕ, gTerm x (2 * k + parity χ + 1) t := by
  have hs : 1 < ((2 : ℂ) + t * I).re := by simp
  have h := ((hasSum_gammaLogDeriv_shift χ hs).mul_right ((x : ℂ) ^ ((2 : ℂ) + t * I))).div_const
    (((2 : ℂ) + t * I) * ((2 : ℂ) + t * I + 1))
  rw [← h.tsum_eq]
  rfl

theorem gammaPartS_eq [NeZero N] (χ : DirichletCharacter ℂ N) (x : ℕ) (hx : 1 ≤ x) :
    gammaPartS χ x = ∑' k : ℕ, (tau x (2 * k + parity χ + 1) : ℂ) := by
  obtain ⟨C, hC0, hC⟩ := perron_pair_integral_norm_le (δ := 1) (θ := 1 / 2) one_pos
    (by norm_num) (by norm_num)
  have hx0 : (0 : ℝ) < x := by exact_mod_cast hx
  have hnorm : ∀ m : ℕ, ∫ t, ‖gTerm x m t‖ ≤
      C * (x : ℝ) ^ (2 : ℝ) * ((1 + (m : ℝ)) ^ (-(1 / 2 : ℝ)) / (2 + m)) := by
    intro m
    obtain ⟨hQi, hQb⟩ := hC x 2 hx0 two_pos (-(m : ℂ)) (by
      simp only [neg_re, natCast_re]; norm_num; linarith [(m.cast_nonneg : (0 : ℝ) ≤ m)])
    simp only [ofReal_natCast, ofReal_ofNat, norm_neg, Complex.norm_natCast] at hQi hQb
    calc ∫ t : ℝ, ‖gTerm x m t‖ ≤ ∫ t : ℝ, 1 / (2 + (m : ℝ)) * ‖(x : ℂ) ^ ((2 : ℂ) + t * I) /
          (((2 : ℂ) + t * I - -(m : ℂ)) * ((2 : ℂ) + t * I + 1))‖ :=
          integral_mono (integrable_gTerm x hx m).norm (hQi.norm.const_mul _)
            (fun t => norm_gTerm_le x m t)
      _ = 1 / (2 + (m : ℝ)) * ∫ t : ℝ, ‖(x : ℂ) ^ ((2 : ℂ) + t * I) /
          (((2 : ℂ) + t * I - -(m : ℂ)) * ((2 : ℂ) + t * I + 1))‖ := integral_const_mul _ _
      _ ≤ 1 / (2 + (m : ℝ)) * (C * (x : ℝ) ^ (2 : ℝ) * (1 + (m : ℝ)) ^ (-(1 / 2 : ℝ))) := by
          gcongr
      _ = _ := by ring
  have hsumm : Summable (fun k : ℕ => ∫ t, ‖gTerm x (2 * k + parity χ + 1) t‖) := by
    refine Summable.of_nonneg_of_le (fun k => integral_nonneg (fun t => norm_nonneg _))
      (fun k => (hnorm _).trans ?_) (summable_rpow32.mul_left (C * (x : ℝ) ^ (2 : ℝ)))
    gcongr
    exact rpow_bound k _ (by omega)
  have hgp : gammaPartS χ x = (1 / (2 * Real.pi) : ℂ) *
      ∫ t : ℝ, ∑' k : ℕ, gTerm x (2 * k + parity χ + 1) t := by
    unfold gammaPartS
    congr 1
    congr 1
    funext t
    exact gamma_integrand_eq χ x t
  rw [hgp, ← integral_tsum_of_summable_integral_norm (fun k => integrable_gTerm x hx _) hsumm,
    ← tsum_mul_left]
  simp_rw [integral_gTerm x hx]

lemma re_gammaLogDeriv_three (χ : DirichletCharacter ℂ N) :
    (gammaLogDeriv χ 3).re = -(1 / 2) * Real.log Real.pi
      + (if parity χ = 0 then 1 - Real.log 2 - Real.eulerMascheroniConstant / 2
          else (1 - Real.eulerMascheroniConstant) / 2) := by
  unfold gammaLogDeriv
  have hp := parity_le_one χ
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hp with h | h
  · rw [h]
    have e : ((3 : ℂ) + ((0 : ℕ) : ℂ)) / 2 = 1 / 2 + 1 := by norm_num
    have hs : ∀ m : ℕ, (1 / 2 : ℂ) ≠ -(m : ℂ) := by
      intro m hm
      have := congrArg Complex.re hm
      simp at this
      linarith [(m.cast_nonneg : (0 : ℝ) ≤ m)]
    rw [e, digamma_apply_add_one _ hs, digamma_one_half]
    have hlog : Complex.log 2 = ((Real.log 2 : ℝ) : ℂ) := by
      rw [Complex.ofReal_log (by norm_num)]; norm_num
    rw [hlog]
    simp only [↓reduceIte, add_re, mul_re, neg_re, ofReal_re, ofReal_im, sub_re, inv_re,
      div_re, one_re, one_im, re_ofNat, im_ofNat, normSq_apply]
    norm_num
    ring
  · rw [h]
    have e : ((3 : ℂ) + ((1 : ℕ) : ℂ)) / 2 = 1 + 1 := by norm_num
    have hs : ∀ m : ℕ, (1 : ℂ) ≠ -(m : ℂ) := by
      intro m hm
      have := congrArg Complex.re hm
      simp at this
      linarith [(m.cast_nonneg : (0 : ℝ) ≤ m)]
    rw [e, digamma_apply_add_one _ hs, digamma_one]
    simp only [one_ne_zero, ↓reduceIte, add_re, mul_re, neg_re, ofReal_re, ofReal_im,
      inv_one, one_re, re_ofNat, im_ofNat]
    norm_num
    ring

/-- The gamma part plus `(1 − 1/x) G(3)` is at most `Eshift x`. -/
theorem re_gamma_shift_le [NeZero N] (χ : DirichletCharacter ℂ N) (x : ℕ) (hx : 1 ≤ x) :
    (gammaPartS χ x + (1 - 1 / (x : ℂ)) * gammaLogDeriv χ 3).re ≤ Eshift x := by
  have hx1 : (1 : ℝ) ≤ x := by exact_mod_cast hx
  have hx0 : (0 : ℝ) < x := by linarith
  set y : ℝ := 1 / x with hy
  have hy0 : 0 < y := by positivity
  have hy1 : y ≤ 1 := by rw [hy, div_le_one hx0]; exact hx1
  have hL : 0 ≤ Real.log x := Real.log_nonneg hx1
  have hfac : (1 - 1 / (x : ℂ)) = ((1 - y : ℝ) : ℂ) := by rw [hy]; push_cast; ring
  rw [gammaPartS_eq χ x hx, hfac, ← Complex.ofReal_tsum, add_re, ofReal_re, re_ofReal_mul,
    re_gammaLogDeriv_three]
  have hl2 := Real.log_two_gt_d9
  have hu := hasSum_u
  unfold Eshift
  rw [← hy]
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp (parity_le_one χ) with h | h
  · -- even: `Σ_k tau(2k+1) = tau 1 + Σ_k tau(2(k+1)+1) ≤ tau 1 + 3y/4`
    rw [h]
    simp only [↓reduceIte, mul_zero, add_zero, zero_add]
    have hS := (tsum_tau_bound x hx1 1 le_rfl).1
    have hS' : Summable (fun k : ℕ => tau x (2 * k + 1)) := by simpa using hS
    rw [hS'.tsum_eq_zero_add]
    have hg : Summable (fun k : ℕ => tau x (2 * (k + 1) + 1)) :=
      (summable_nat_add_iff (f := fun k : ℕ => tau x (2 * k + 1)) 1).mpr hS'
    have hle : ∑' k : ℕ, tau x (2 * (k + 1) + 1) ≤ 3 * y / 4 := by
      have := Summable.tsum_le_tsum (fun k => tau_le_odd x hx1 k) hg (hu.summable.mul_left _)
      rwa [tsum_mul_left, hu.tsum_eq, mul_one, ← hy] at this
    have ht1 : tau x (2 * 0 + 1) = (1 - y) / 3 - (1 - y - y * Real.log x) := by
      simp [tau, hy]
    rw [ht1]
    have hl2' : Real.log 2 < 1 := by
      have := Real.log_two_lt_d9; linarith
    have h1 : y * Real.log 2 ≤ y := by nlinarith
    have h2 : (Real.log x + 2) / x = y * Real.log x + 2 * y := by rw [hy]; field_simp
    rw [h2]
    nlinarith
  · -- odd: `Σ_k tau(2k+2) = Σ_k tau(2(k+1)) ≤ (3y − 1)/2`
    rw [h]
    simp only [one_ne_zero, ↓reduceIte]
    have hS := (tsum_tau_bound x hx1 0 (by norm_num)).1
    have hS' : Summable (fun k : ℕ => tau x (2 * k)) := by simpa using hS
    have hg : Summable (fun k : ℕ => tau x (2 * (k + 1))) :=
      (summable_nat_add_iff (f := fun k : ℕ => tau x (2 * k)) 1).mpr hS'
    have he : (fun k : ℕ => tau x (2 * k + 1 + 1)) = fun k : ℕ => tau x (2 * (k + 1)) := by
      funext k; congr 1
    rw [he]
    have hle : ∑' k : ℕ, tau x (2 * (k + 1)) ≤ (3 * y - 1) / 2 := by
      have := Summable.tsum_le_tsum (fun k => tau_le_even x hx1 k) hg (hu.summable.mul_left _)
      rwa [tsum_mul_left, hu.tsum_eq, mul_one, ← hy] at this
    have h2 : (Real.log x + 2) / x = y * Real.log x + 2 * y := by rw [hy]; field_simp
    rw [h2]
    nlinarith [mul_nonneg hy0.le hL]

end LLS.ShiftAux
