import LLS.Analytic.Log.Perron

/-!
# The gamma-factor term of the log-weighted explicit formula

`G(s) − G(2) = Σ_k (1/(2+m_k) − 1/(s+m_k))`, `m_k = 2k + 𝔞` (erdos-985's digamma series).
Against `x^s/s²` the `m`-th term integrates to `ltau x m`:
`log x/(2+m) − log x/m + (1 − x^{−m})/m²` for `m ≥ 1` (poles at `−m` and `0`), and
`log x/2 − (log x)²/2` for `m = 0` (triple pole at `0`). Summing,
`Re (Γ̃(x) + G(2) log x) ≤ −½ log π · log x + π²/6 − (γ/2) log x`.
-/

namespace LLS.LogAux

open Complex MeasureTheory Erdos985.Analytic Erdos985.Analytic.PerronAux Erdos985.Analytic.BoundsAux

/-- The `m`-th term of the gamma-part integrand for the log kernel. -/
noncomputable def lgTerm (x : ℕ) (m : ℕ) (t : ℝ) : ℂ :=
  (1 / (2 + (m : ℂ)) - 1 / (((2 : ℂ) + t * I) + (m : ℂ))) * lkern x t

lemma lgTerm_eq_gTerm (x m : ℕ) (t : ℝ) :
    lgTerm x m t = gTerm x m t * (((2 : ℂ) + t * I + 1) / ((2 : ℂ) + t * I)) := by
  unfold lgTerm gTerm
  rw [lkern_eq]
  unfold IdentityAux.kern
  push_cast
  ring

lemma continuous_lgTerm {x : ℕ} (hx : 1 ≤ x) (m : ℕ) : Continuous (lgTerm x m) := by
  have hx0 : (0 : ℝ) < x := by exact_mod_cast hx
  unfold lgTerm
  have hne : ∀ t : ℝ, (2 : ℂ) + t * I + m ≠ 0 := fun t h => by
    have := congrArg Complex.re h; simp at this; linarith [(m.cast_nonneg : (0 : ℝ) ≤ m)]
  have h1 : Continuous fun t : ℝ => ((2 : ℂ) + t * I + m) := continuous_line.add continuous_const
  have h2 : Continuous fun t : ℝ => 1 / ((2 : ℂ) + t * I + m) := by
    simp only [one_div]; exact h1.inv₀ hne
  exact (continuous_const.sub h2).mul (continuous_lkern hx0)

lemma integrable_lgTerm {x : ℕ} (hx : 1 ≤ x) (m : ℕ) : Integrable (lgTerm x m) := by
  refine integrable_of_le_mul (integrable_gTerm x hx m) (continuous_lgTerm hx m) (3 / 2)
    fun t => ?_
  rw [lgTerm_eq_gTerm, norm_mul, mul_comm]
  exact mul_le_mul_of_nonneg_right (norm_add_one_div_le t) (norm_nonneg _)

/-- The value of `(1/2π) ∫ lgTerm x m`. -/
noncomputable def ltau (x : ℝ) (m : ℕ) : ℝ :=
  if m = 0 then Real.log x / 2 - Real.log x ^ 2 / 2
  else Real.log x / (2 + m) - Real.log x / m + (1 - 1 / x ^ m) / (m : ℝ) ^ 2

lemma integral_lgTerm {x : ℕ} (hx : 1 ≤ x) (m : ℕ) :
    (1 / (2 * Real.pi) : ℂ) * ∫ t : ℝ, lgTerm x m t = (ltau x m : ℂ) := by
  have hx0 : (0 : ℝ) < x := by exact_mod_cast hx
  have hx1 : (1 : ℝ) ≤ x := by exact_mod_cast hx
  have hpi : (2 * (Real.pi : ℂ)) ≠ 0 := mul_ne_zero two_ne_zero (ofReal_ne_zero.2 Real.pi_pos.ne')
  have hK : (1 / (2 * Real.pi) : ℂ) * ∫ t, lkern x t = (Real.log x : ℂ) := by
    rw [integral_lkern hx1, ← mul_assoc, one_div_mul_cancel hpi, one_mul]
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · have e : lgTerm x 0 = fun t => (1 / 2 : ℂ) * lkern x t -
        (x : ℂ) ^ ((2 : ℂ) + t * I) / ((2 : ℂ) + t * I) ^ 3 := by
      funext t
      unfold lgTerm lkern
      have := line_ne_zero2 t
      rw [show ((0 : ℕ) : ℂ) = 0 by simp, add_zero, add_zero]
      simp only [ofReal_natCast]
      field_simp
    have hc : Integrable fun t : ℝ => (x : ℂ) ^ ((2 : ℂ) + t * I) / ((2 : ℂ) + t * I) ^ 3 := by
      have : (fun t : ℝ => (x : ℂ) ^ ((2 : ℂ) + t * I) / ((2 : ℂ) + t * I) ^ 3)
          = fun t : ℝ => (2 + t * I : ℂ)⁻¹ * lkern x t := by
        funext t; unfold lkern; have := line_ne_zero2 t; push_cast; field_simp
      rw [this]
      refine integrable_of_le_mul (integrable_lkern hx0) ?_ (1 / 2) fun t => ?_
      · exact (continuous_line.inv₀ line_ne_zero2).mul (continuous_lkern hx0)
      · rw [norm_mul]; exact mul_le_mul_of_nonneg_right (norm_inv_line_le t) (norm_nonneg _)
    have h3 := perron_cube (x : ℝ) hx1
    push_cast at h3
    rw [e, integral_sub ((integrable_lkern hx0).const_mul _) hc, integral_const_mul, mul_sub,
      mul_left_comm, hK, h3]
    simp [ltau]
    ring
  · have hm0 : m ≠ 0 := by omega
    have hw : (-(m : ℂ)).re < 2 := hw_m m
    have hw0 : -(m : ℂ) ≠ 0 := by simpa using hm0
    have e : lgTerm x m = fun t => (1 / (2 + (m : ℂ))) * lkern x t - lres x (-(m : ℂ)) t := by
      funext t
      unfold lgTerm lres
      rw [sub_mul]
      congr 1
      unfold lkern
      have h0 := line_ne_zero2 t
      have h2 : (2 : ℂ) + t * I + m ≠ 0 := fun h => by
        have := congrArg Complex.re h; simp at this; linarith [(m.cast_nonneg : (0 : ℝ) ≤ m)]
      rw [sub_neg_eq_add]
      field_simp
    have hR := perron_lres (x : ℝ) hx1 _ hw hw0
    rw [e, integral_sub ((integrable_lkern hx0).const_mul _) (integrable_lres hx0 hw),
      integral_const_mul, mul_sub, mul_left_comm, hK, hR]
    simp only [ltau, hm0, ↓reduceIte]
    have hmc : (m : ℂ) ≠ 0 := by exact_mod_cast hm0
    have hxc : (x : ℂ) ≠ 0 := by exact_mod_cast (show x ≠ 0 by omega)
    have h2m : (2 : ℂ) + m ≠ 0 := by
      intro h; have := congrArg Complex.re h; simp at this; linarith [(m.cast_nonneg : (0 : ℝ) ≤ m)]
    rw [cpow_neg, cpow_natCast]
    push_cast
    field_simp
    ring

lemma integral_norm_lgTerm_le :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (x : ℕ), 1 ≤ x → ∀ m : ℕ, ∫ t, ‖lgTerm x m t‖ ≤
      C * (x : ℝ) ^ (2 : ℝ) * ((1 + (m : ℝ)) ^ (-(1 / 2 : ℝ)) / (2 + m)) := by
  obtain ⟨C, hC0, hC⟩ := perron_pair_integral_norm_le (δ := 1) (θ := 1 / 2) one_pos
    (by norm_num) (by norm_num)
  refine ⟨3 / 2 * C, by positivity, fun x hx m => ?_⟩
  have hx0 : (0 : ℝ) < x := by exact_mod_cast hx
  obtain ⟨hQi, hQb⟩ := hC x 2 hx0 two_pos (-(m : ℂ)) (by
    simp only [neg_re, natCast_re]; norm_num; linarith [(m.cast_nonneg : (0 : ℝ) ≤ m)])
  simp only [ofReal_natCast, ofReal_ofNat, norm_neg, Complex.norm_natCast] at hQi hQb
  have hpt : ∀ t, ‖lgTerm x m t‖ ≤ 3 / 2 * (1 / (2 + (m : ℝ)) * ‖(x : ℂ) ^ ((2 : ℂ) + t * I) /
          (((2 : ℂ) + t * I - -(m : ℂ)) * ((2 : ℂ) + t * I + 1))‖) := fun t => by
    rw [lgTerm_eq_gTerm, norm_mul, mul_comm]
    exact mul_le_mul (norm_add_one_div_le t) (norm_gTerm_le x m t) (norm_nonneg _) (by norm_num)
  calc ∫ t : ℝ, ‖lgTerm x m t‖ ≤ ∫ t : ℝ, 3 / 2 * (1 / (2 + (m : ℝ)) *
        ‖(x : ℂ) ^ ((2 : ℂ) + t * I) / (((2 : ℂ) + t * I - -(m : ℂ)) * ((2 : ℂ) + t * I + 1))‖) :=
        integral_mono (integrable_lgTerm hx m).norm ((hQi.norm.const_mul _).const_mul _) hpt
    _ = 3 / 2 * (1 / (2 + (m : ℝ)) * ∫ t : ℝ, ‖(x : ℂ) ^ ((2 : ℂ) + t * I) /
          (((2 : ℂ) + t * I - -(m : ℂ)) * ((2 : ℂ) + t * I + 1))‖) := by
        rw [integral_const_mul, integral_const_mul]
    _ ≤ 3 / 2 * (1 / (2 + (m : ℝ)) * (C * (x : ℝ) ^ (2 : ℝ) * (1 + (m : ℝ)) ^ (-(1 / 2 : ℝ)))) := by
        gcongr
    _ = _ := by ring

variable {N : ℕ} [NeZero N]

/-- The gamma-factor part of the log-weighted explicit formula. -/
noncomputable def lgammaPart (χ : DirichletCharacter ℂ N) (x : ℕ) : ℂ :=
  (1 / (2 * Real.pi) : ℂ) * ∫ t : ℝ,
    (gammaLogDeriv χ (2 + t * I) - gammaLogDeriv χ 2) * lkern x t

theorem lgammaPart_eq (χ : DirichletCharacter ℂ N) (x : ℕ) (hx : 1 ≤ x) :
    Summable (fun k : ℕ => ltau x (2 * k + parity χ)) ∧
    lgammaPart χ x = ((∑' k : ℕ, ltau x (2 * k + parity χ) : ℝ) : ℂ) := by
  obtain ⟨C, hC0, hC⟩ := integral_norm_lgTerm_le
  have hsum : ∀ t : ℝ, (gammaLogDeriv χ (2 + t * I) - gammaLogDeriv χ 2) * lkern x t =
      ∑' k : ℕ, lgTerm x (2 * k + parity χ) t := by
    intro t
    have hs : 1 < ((2 : ℂ) + t * I).re := by simp
    exact ((hasSum_gammaLogDeriv χ hs).mul_right _).tsum_eq.symm
  have hsumm : Summable (fun k : ℕ => ∫ t, ‖lgTerm x (2 * k + parity χ) t‖) := by
    refine Summable.of_nonneg_of_le (fun k => integral_nonneg (fun t => norm_nonneg _))
      (fun k => (hC x hx _).trans ?_) (summable_rpow32.mul_left (C * (x : ℝ) ^ (2 : ℝ)))
    gcongr
    exact rpow_bound k _ (by omega)
  have hval : lgammaPart χ x = ∑' k : ℕ, (ltau x (2 * k + parity χ) : ℂ) := by
    unfold lgammaPart
    rw [show (fun t : ℝ => (gammaLogDeriv χ (2 + t * I) - gammaLogDeriv χ 2) * lkern x t)
        = fun t => ∑' k : ℕ, lgTerm x (2 * k + parity χ) t from funext hsum,
      ← integral_tsum_of_summable_integral_norm (fun k => integrable_lgTerm hx _) hsumm,
      ← tsum_mul_left]
    simp_rw [integral_lgTerm hx]
  -- summability of the real values
  have hsR : Summable (fun k : ℕ => ltau x (2 * k + parity χ)) := by
    have hs2 : Summable (fun k : ℕ => (1 / (2 * Real.pi) : ℂ) *
        ∫ t, lgTerm x (2 * k + parity χ) t) := by
      refine Summable.of_norm_bounded (hsumm.mul_left (1 / (2 * Real.pi))) fun k => ?_
      rw [norm_mul]
      have : ‖(1 / (2 * Real.pi) : ℂ)‖ = 1 / (2 * Real.pi) := by
        rw [norm_div, norm_one, norm_mul, Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le]
        simp
      rw [this]
      gcongr
      exact norm_integral_le_integral_norm _
    simp_rw [integral_lgTerm hx] at hs2
    exact (Complex.summable_ofReal).1 hs2
  exact ⟨hsR, by rw [hval, Complex.ofReal_tsum]⟩

lemma ltau_le_even (x : ℝ) (hx : 1 ≤ x) (k : ℕ) :
    ltau x (2 * k) ≤ 1 / ((k : ℝ) + 1) ^ 2 + (if k = 0 then 1 / 8 - 1 else 0) := by
  have hl : 0 ≤ Real.log x := Real.log_nonneg hx
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp only [ltau, mul_zero, ↓reduceIte]
    nlinarith [sq_nonneg (Real.log x - 1 / 2)]
  · have hm : 2 * k ≠ 0 := by omega
    simp only [ltau, hm, ↓reduceIte, (show k ≠ 0 by omega), add_zero]
    have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk
    have hmR : ((2 * k : ℕ) : ℝ) = 2 * k := by push_cast; ring
    rw [hmR]
    have h1 : Real.log x / (2 + 2 * k) - Real.log x / (2 * k) ≤ 0 := by
      have : Real.log x / (2 + 2 * k) ≤ Real.log x / (2 * k) :=
        div_le_div_of_nonneg_left hl (by positivity) (by linarith)
      linarith
    have hxm : 0 ≤ 1 / x ^ (2 * k) := by positivity
    have h2 : (1 - 1 / x ^ (2 * k)) / (2 * (k : ℝ)) ^ 2 ≤ 1 / ((k : ℝ) + 1) ^ 2 := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith
    linarith

lemma ltau_le_odd (x : ℝ) (hx : 1 ≤ x) (k : ℕ) :
    ltau x (2 * k + 1) ≤ 1 / ((k : ℝ) + 1) ^ 2 + (if k = 0 then -(2 / 3) * Real.log x else 0) := by
  have hl : 0 ≤ Real.log x := Real.log_nonneg hx
  have hm : 2 * k + 1 ≠ 0 := by omega
  simp only [ltau, hm, ↓reduceIte]
  have hmR : ((2 * k + 1 : ℕ) : ℝ) = 2 * k + 1 := by push_cast; ring
  rw [hmR]
  have hxm : 0 ≤ 1 / x ^ (2 * k + 1) := by positivity
  have h2 : (1 - 1 / x ^ (2 * k + 1)) / (2 * (k : ℝ) + 1) ^ 2 ≤ 1 / ((k : ℝ) + 1) ^ 2 := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have : (0 : ℝ) ≤ k := k.cast_nonneg
    nlinarith
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp only [Nat.cast_zero, mul_zero, zero_add, ↓reduceIte] at h2 ⊢
    norm_num at h2 ⊢
    have : 0 ≤ x⁻¹ := by positivity
    linarith
  · simp only [(show k ≠ 0 by omega), ↓reduceIte, add_zero]
    have h1 : Real.log x / (2 + (2 * k + 1)) - Real.log x / (2 * k + 1) ≤ 0 := by
      have : Real.log x / (2 + (2 * k + 1)) ≤ Real.log x / (2 * k + 1) :=
        div_le_div_of_nonneg_left hl (by positivity) (by linarith)
      linarith
    linarith

lemma hasSum_inv_succ_sq : HasSum (fun k : ℕ => 1 / ((k : ℝ) + 1) ^ 2) (Real.pi ^ 2 / 6) := by
  have := (hasSum_nat_add_iff (f := fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ 2) 1).2
    (by simpa using hasSum_zeta_two)
  simpa using this

lemma hasSum_bound (e : ℝ) : HasSum (fun k : ℕ => 1 / ((k : ℝ) + 1) ^ 2 +
    (if k = 0 then e else 0)) (Real.pi ^ 2 / 6 + e) := by
  refine hasSum_inv_succ_sq.add ?_
  have := hasSum_ite_eq (0 : ℕ) e
  simpa [eq_comm] using this

lemma re_digamma_three_halves_le :
    (Complex.digamma (3 / 2)).re ≤ 1 - Real.eulerMascheroniConstant := by
  have h := hasSum_digamma (w := (3 / 2 : ℂ)) (by norm_num)
  have hre := Complex.reCLM.hasSum h
  have e : ∀ k : ℕ, Complex.reCLM (1 / ((k : ℂ) + 1) - 1 / ((k : ℂ) + 3 / 2))
      = 1 / ((k : ℝ) + 1) - 1 / ((k : ℝ) + 3 / 2) := fun k => by
    have : (1 / ((k : ℂ) + 1) - 1 / ((k : ℂ) + 3 / 2))
        = ((1 / ((k : ℝ) + 1) - 1 / ((k : ℝ) + 3 / 2) : ℝ) : ℂ) := by push_cast; ring
    rw [this, Complex.reCLM_apply, Complex.ofReal_re]
  simp only [e] at hre
  have hle := hasSum_le (fun k => ?_) hre hasSum_u
  · simp only [Complex.reCLM_apply, sub_re, Complex.digamma_one, neg_re, ofReal_re] at hle
    linarith
  · have hk : (0 : ℝ) ≤ k := k.cast_nonneg
    rw [div_sub_div _ _ (by positivity) (by positivity), div_le_div_iff₀ (by positivity)
      (by positivity)]
    nlinarith

theorem re_lgammaPart_le (χ : DirichletCharacter ℂ N) (x : ℕ) (hx : 1 ≤ x) :
    (lgammaPart χ x + gammaLogDeriv χ 2 * (Real.log x : ℂ)).re
      ≤ -(1 / 2) * Real.log Real.pi * Real.log x + Etil x := by
  obtain ⟨hs, he⟩ := lgammaPart_eq χ x hx
  have hx1 : (1 : ℝ) ≤ x := by exact_mod_cast hx
  have hl : 0 ≤ Real.log x := Real.log_nonneg hx1
  rw [he, add_re, ofReal_re, re_mul_ofReal]
  unfold Etil
  unfold gammaLogDeriv
  rcases Nat.le_one_iff_eq_zero_or_eq_one.1 (parity_le_one χ) with h0 | h1
  · rw [h0]
    have hb := hasSum_bound (1 / 8 - 1)
    have hle := hs.tsum_le_tsum (fun k => ?_) hb.summable
    · rw [hb.tsum_eq, h0] at hle
      have hg : ((-(1 / 2) * (Real.log Real.pi : ℂ) + 1 / 2 *
          Complex.digamma ((2 + ((0 : ℕ) : ℂ)) / 2))).re
            = -(1 / 2) * Real.log Real.pi - 1 / 2 * Real.eulerMascheroniConstant := by
        rw [show (2 + ((0 : ℕ) : ℂ)) / 2 = 1 by norm_num, Complex.digamma_one]
        simp
        ring
      rw [hg]
      have : Real.pi ^ 2 / 6 + (1 / 8 - 1) ≤ Real.pi ^ 2 / 6 := by norm_num
      nlinarith
    · simpa [h0] using ltau_le_even (x : ℝ) hx1 k
  · rw [h1]
    have hb := hasSum_bound (-(2 / 3) * Real.log x)
    have hle := hs.tsum_le_tsum (fun k => ?_) hb.summable
    · rw [hb.tsum_eq, h1] at hle
      have hg : ((-(1 / 2) * (Real.log Real.pi : ℂ) + 1 / 2 *
          Complex.digamma ((2 + ((1 : ℕ) : ℂ)) / 2))).re
            = -(1 / 2) * Real.log Real.pi + 1 / 2 * (Complex.digamma (3 / 2)).re := by
        rw [show (2 + ((1 : ℕ) : ℂ)) / 2 = 3 / 2 by norm_num]
        simp
      rw [hg]
      have hd := re_digamma_three_halves_le
      nlinarith
    · simpa [h1] using ltau_le_odd (x : ℝ) hx1 k

end LLS.LogAux
