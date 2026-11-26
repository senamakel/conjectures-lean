import LLS.L1.Shift

/-!
# LLS Lemma 2.5: `log |L(1, χ)|` from the shifted formula, integrated over `σ ∈ (1, ∞)`

For real `σ ≥ 1` put
`H(σ) = Re A(σ) + log x · log |L(σ)| + Re (L'/L)(σ)`, with
`A(σ) = −Σ_{n≤x} Λ(n)χ(n) log(x/n) n^{−σ}/log n`. Then `H'(σ)` is the real part of the
expression bounded in `LLS.shifted_log_bound`, so `|H'(σ)| ≤ e(σ) = x^{1/2−σ} Z2 + 2x^{−σ}`
for `σ > 1`. With `P(σ) = −(x^{1/2−σ} Z2 + 2x^{−σ})/log x` (so `P' = e`), both `H + P` and
`P − H` are monotone on `[1, ∞)`. Since `H(T), P(T) → 0` as `T → ∞`, `|H(1)| ≤ −P(1)`, which is
the lemma after dividing by `log x`. No integral over `σ` is needed.
-/

namespace LLS

open Complex ArithmeticFunction Erdos985 Filter Topology Set

namespace L1Int

variable {N : ℕ} [NeZero N]

/-- `Λ(n)χ(n) log(x/n)/log n`. -/
noncomputable def coef (χ : DirichletCharacter ℂ N) (x n : ℕ) : ℂ :=
  (Λ n : ℂ) * χ n * (Real.log ((x : ℝ) / n) : ℂ) / (Real.log n : ℂ)

lemma vM_lt_two {n : ℕ} (h : n < 2) : (Λ n : ℝ) = 0 := by
  interval_cases n <;> simp

lemma coef_mul_log (χ : DirichletCharacter ℂ N) (x n : ℕ) :
    coef χ x n * (Real.log n : ℂ) = (Λ n : ℂ) * χ n * (Real.log ((x : ℝ) / n) : ℂ) := by
  rcases lt_or_ge n 2 with h | h
  · simp [coef, vM_lt_two h]
  · have h1 : (1 : ℝ) < n := by exact_mod_cast h
    have : (Real.log n : ℂ) ≠ 0 := ofReal_ne_zero.2 (Real.log_pos h1).ne'
    unfold coef
    field_simp

/-- The antiderivative of the finite sum. -/
noncomputable def Acx (χ : DirichletCharacter ℂ N) (x : ℕ) (z : ℂ) : ℂ :=
  ∑ n ∈ Finset.range (x + 1), coef χ x n * (-(n : ℂ) ^ (-z))

lemma hasDerivAt_Acx (χ : DirichletCharacter ℂ N) (x : ℕ) {z : ℂ} (hz : z ≠ 0) :
    HasDerivAt (Acx χ x) (∑ n ∈ Finset.range (x + 1),
      (Λ n : ℂ) * χ n * (n : ℂ) ^ (-z) * (Real.log ((x : ℝ) / n) : ℂ)) z := by
  have h : ∀ n ∈ Finset.range (x + 1), HasDerivAt (fun w => coef χ x n * (-(n : ℂ) ^ (-w)))
      ((Λ n : ℂ) * χ n * (n : ℂ) ^ (-z) * (Real.log ((x : ℝ) / n) : ℂ)) z := by
    intro n _
    have h1 : HasDerivAt (fun w : ℂ => (n : ℂ) ^ (-w)) ((n : ℂ) ^ (-z) * Complex.log n * (-1)) z :=
      (hasDerivAt_neg z).const_cpow (Or.inr (neg_ne_zero.2 hz))
    have h2 := h1.neg.const_mul (coef χ x n)
    convert h2 using 1
    rw [← Complex.natCast_log]
    rw [show coef χ x n * -((n : ℂ) ^ (-z) * (Real.log n : ℂ) * -1)
        = (coef χ x n * (Real.log n : ℂ)) * (n : ℂ) ^ (-z) by ring, coef_mul_log]
    ring
  have := HasDerivAt.fun_sum h
  unfold Acx
  exact this

/-- `log |L(t)|`, written through `normSq` so that it is differentiable where `L ≠ 0`. -/
noncomputable def Bf (χ : DirichletCharacter ℂ N) (t : ℝ) : ℝ :=
  (1 / 2) * Real.log ((DirichletCharacter.LFunction χ t).re ^ 2
    + (DirichletCharacter.LFunction χ t).im ^ 2)

lemma Bf_eq (χ : DirichletCharacter ℂ N) (t : ℝ) :
    Bf χ t = Real.log ‖DirichletCharacter.LFunction χ t‖ := by
  unfold Bf
  rw [Complex.norm_def, Real.log_sqrt (normSq_nonneg _), normSq_apply]
  ring_nf

lemma L_ne_zero {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1) {t : ℝ} (ht : 1 ≤ t) :
    DirichletCharacter.LFunction χ t ≠ 0 :=
  DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inl hχ) (by simpa using ht)

lemma hasDerivAt_Bf {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1) {t : ℝ} (ht : 1 ≤ t) :
    HasDerivAt (Bf χ)
      (deriv (DirichletCharacter.LFunction χ) t / DirichletCharacter.LFunction χ t).re t := by
  set L := DirichletCharacter.LFunction χ
  have hLd : Differentiable ℂ L := DirichletCharacter.differentiable_LFunction hχ
  have hL : HasDerivAt L (deriv L t) (t : ℂ) := (hLd (t : ℂ)).hasDerivAt
  have hR : HasDerivAt (fun x : ℝ => (L x).re) (deriv L t).re t := hL.real_of_complex
  have hI' : HasDerivAt (fun x : ℝ => (-I * L x).re) (-I * deriv L t).re t :=
    (hL.const_mul (-I)).real_of_complex
  have eI : (fun x : ℝ => (-I * L x).re) = fun x : ℝ => (L x).im := by
    funext x; simp
  rw [eI] at hI'
  have hIre : (-I * deriv L t).re = (deriv L t).im := by simp
  rw [hIre] at hI'
  have hne := L_ne_zero hχ ht
  have hQ : (L t).re ^ 2 + (L t).im ^ 2 ≠ 0 := by
    have := (normSq_pos.2 hne).ne'
    rw [normSq_apply] at this
    convert this using 1; ring
  have hD := (((hR.pow 2).add (hI'.pow 2)).log hQ).const_mul (1 / 2)
  unfold Bf
  convert hD using 1
  simp only [Pi.add_apply, Pi.pow_apply]
  rw [div_re, normSq_apply]
  field_simp
  ring

/-- `(L'/L)(s)`. -/
noncomputable def F (χ : DirichletCharacter ℂ N) (s : ℂ) : ℂ :=
  deriv (DirichletCharacter.LFunction χ) s / DirichletCharacter.LFunction χ s

lemma differentiableAt_F {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1) {s : ℂ}
    (hs : DirichletCharacter.LFunction χ s ≠ 0) : DifferentiableAt ℂ (F χ) s := by
  have hLd : Differentiable ℂ (DirichletCharacter.LFunction χ) :=
    DirichletCharacter.differentiable_LFunction hχ
  have hd : DifferentiableAt ℂ (deriv (DirichletCharacter.LFunction χ)) s :=
    (hLd.analyticAt s).deriv.differentiableAt
  exact hd.div (hLd s) hs

/-- The function whose derivative is bounded by `shifted_log_bound`. -/
noncomputable def H (χ : DirichletCharacter ℂ N) (x : ℕ) (σ : ℝ) : ℝ :=
  (Acx χ x σ).re + Real.log x * Bf χ σ + (F χ σ).re

/-- Its derivative. -/
noncomputable def Hd (χ : DirichletCharacter ℂ N) (x : ℕ) (σ : ℝ) : ℂ :=
  (∑ n ∈ Finset.range (x + 1),
      (Λ n : ℂ) * χ n * (n : ℂ) ^ (-(σ : ℂ)) * (Real.log ((x : ℝ) / n) : ℂ))
    + deriv (DirichletCharacter.LFunction χ) σ / DirichletCharacter.LFunction χ σ
        * (Real.log x : ℂ)
    + deriv (fun s => deriv (DirichletCharacter.LFunction χ) s
        / DirichletCharacter.LFunction χ s) σ

lemma hasDerivAt_H {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1) (x : ℕ) {σ : ℝ} (hσ : 1 ≤ σ) :
    HasDerivAt (H χ x) (Hd χ x σ).re σ := by
  have hσ0 : (σ : ℂ) ≠ 0 := by
    rw [Ne, ofReal_eq_zero]; linarith
  have h1 := (hasDerivAt_Acx χ x hσ0).real_of_complex
  have h2 := (hasDerivAt_Bf hχ hσ).const_mul (Real.log x)
  have hF := (differentiableAt_F hχ (L_ne_zero hχ hσ)).hasDerivAt.real_of_complex
  have h := (h1.add h2).add hF
  unfold H
  convert h using 1
  unfold Hd F
  simp only [add_re, re_mul_ofReal]
  ring

lemma continuousOn_H {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1) (x : ℕ) :
    ContinuousOn (H χ x) (Ici 1) :=
  fun σ hσ => (hasDerivAt_H hχ x hσ).continuousAt.continuousWithinAt

/-! ### The comparison function `P` -/

/-- `−(x^{1/2−σ} Z + 2x^{−σ})/log x`. -/
noncomputable def P (x Z σ : ℝ) : ℝ := -(x ^ ((1 : ℝ) / 2 - σ) * Z + 2 * x ^ (-σ)) / Real.log x

lemma hasDerivAt_P {x : ℝ} (hx : 1 < x) (Z σ : ℝ) :
    HasDerivAt (P x Z) (x ^ ((1 : ℝ) / 2 - σ) * Z + 2 * x ^ (-σ)) σ := by
  have hx0 : 0 < x := by linarith
  have hl : Real.log x ≠ 0 := (Real.log_pos hx).ne'
  have a1 : HasDerivAt (fun σ : ℝ => x ^ ((1 : ℝ) / 2 - σ))
      (x ^ ((1 : ℝ) / 2 - σ) * Real.log x * (-1)) σ :=
    (Real.hasStrictDerivAt_const_rpow hx0 _).hasDerivAt.comp σ ((hasDerivAt_id σ).const_sub _)
  have a2 : HasDerivAt (fun σ : ℝ => x ^ (-σ)) (x ^ (-σ) * Real.log x * (-1)) σ :=
    (Real.hasStrictDerivAt_const_rpow hx0 _).hasDerivAt.comp σ (hasDerivAt_id σ).neg
  have h := (((a1.mul_const Z).add (a2.const_mul 2)).neg).div_const (Real.log x)
  unfold P
  convert h using 1
  field_simp
  ring

lemma tendsto_rpow_sub (x c : ℝ) (hx : 1 < x) :
    Tendsto (fun T : ℝ => x ^ (c - T)) atTop (𝓝 0) := by
  have hx0 : 0 < x := by linarith
  have h : Tendsto (fun T : ℝ => x⁻¹ ^ T) atTop (𝓝 0) :=
    tendsto_rpow_atTop_of_base_lt_one _ (by linarith [inv_pos.2 hx0])
      (inv_lt_one_of_one_lt₀ hx)
  have e : ∀ T : ℝ, x ^ (c - T) = x ^ c * x⁻¹ ^ T := fun T => by
    rw [Real.inv_rpow hx0.le, ← Real.rpow_neg hx0.le, ← Real.rpow_add hx0, sub_eq_add_neg]
  simp_rw [e]
  simpa using h.const_mul (x ^ c)

lemma tendsto_P {x : ℝ} (hx : 1 < x) (Z : ℝ) : Tendsto (P x Z) atTop (𝓝 0) := by
  have h1 := tendsto_rpow_sub x ((1 : ℝ) / 2) hx
  have h2 := tendsto_rpow_sub x 0 hx
  simp only [zero_sub] at h2
  have := (((h1.mul_const Z).add (h2.const_mul 2)).neg).div_const (Real.log x)
  rw [show -(0 * Z + 2 * 0) / Real.log x = (0 : ℝ) by simp] at this
  exact this

/-! ### `H(T) → 0` -/

lemma tendsto_Acx (χ : DirichletCharacter ℂ N) (x : ℕ) :
    Tendsto (fun T : ℝ => Acx χ x T) atTop (𝓝 0) := by
  have h : ∀ n ∈ Finset.range (x + 1),
      Tendsto (fun T : ℝ => coef χ x n * (-(n : ℂ) ^ (-(T : ℂ)))) atTop (𝓝 0) := by
    intro n _
    rcases lt_or_ge n 2 with hn | hn
    · simp [coef, vM_lt_two hn]
    · have hn1 : (1 : ℝ) < n := by exact_mod_cast hn
      have hnorm : Tendsto (fun T : ℝ => ‖(n : ℂ) ^ (-(T : ℂ))‖) atTop (𝓝 0) := by
        have e : ∀ T : ℝ, ‖(n : ℂ) ^ (-(T : ℂ))‖ = (n : ℝ) ^ ((0 : ℝ) - T) := fun T => by
          rw [norm_natCast_cpow_of_pos (by omega)]; simp
        simp_rw [e]
        exact tendsto_rpow_sub _ 0 hn1
      have h0 : Tendsto (fun T : ℝ => (n : ℂ) ^ (-(T : ℂ))) atTop (𝓝 0) :=
        tendsto_zero_iff_norm_tendsto_zero.2 hnorm
      simpa using (h0.neg).const_mul (coef χ x n)
  have := tendsto_finsetSum (Finset.range (x + 1)) h
  simp only [Finset.sum_const_zero] at this
  exact this

lemma tendsto_L (χ : DirichletCharacter ℂ N) :
    Tendsto (fun T : ℝ => DirichletCharacter.LFunction χ T) atTop (𝓝 1) := by
  have ha : LSeries.abscissaOfAbsConv (fun n : ℕ => χ n) < ⊤ := by
    have := (DirichletCharacter.LSeriesSummable_of_one_lt_re χ (s := 2) (by norm_num)).abscissaOfAbsConv_le
    exact lt_of_le_of_lt this (by simp)
  have h := LSeries.tendsto_atTop ha
  simp only [Nat.cast_one, map_one] at h
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop 1] with T hT
  rw [DirichletCharacter.LFunction_eq_LSeries χ (by simpa using hT)]

lemma tendsto_F (χ : DirichletCharacter ℂ N) :
    Tendsto (fun T : ℝ => F χ T) atTop (𝓝 0) := by
  have ha : LSeries.abscissaOfAbsConv ((fun n : ℕ => χ n) * fun n : ℕ => (Λ n : ℂ)) < ⊤ := by
    have := (DirichletCharacter.LSeriesSummable_twist_vonMangoldt χ (s := 2)
      (by norm_num)).abscissaOfAbsConv_le
    exact lt_of_le_of_lt this (by simp)
  have h := LSeries.tendsto_atTop ha
  simp only [Pi.mul_apply, Nat.cast_one, map_one, vonMangoldt_apply_one, ofReal_zero,
    mul_zero] at h
  have h' := h.neg
  rw [neg_zero] at h'
  refine h'.congr' ?_
  filter_upwards [eventually_gt_atTop 1] with T hT
  have hz : 1 < ((T : ℂ)).re := by simpa using hT
  have h1 := DirichletCharacter.LSeries_twist_vonMangoldt_eq χ hz
  rw [← DirichletCharacter.LFunction_eq_LSeries χ hz,
    ← DirichletCharacter.deriv_LFunction_eq_deriv_LSeries χ hz] at h1
  unfold F
  rw [h1, neg_div, neg_neg]

lemma tendsto_Bf (χ : DirichletCharacter ℂ N) : Tendsto (Bf χ) atTop (𝓝 0) := by
  have hL := tendsto_L χ
  have hre := (continuous_re.tendsto 1).comp hL
  have him := (continuous_im.tendsto 1).comp hL
  have hQ : Tendsto (fun t : ℝ => (DirichletCharacter.LFunction χ t).re ^ 2
      + (DirichletCharacter.LFunction χ t).im ^ 2) atTop (𝓝 ((1 : ℂ).re ^ 2 + (1 : ℂ).im ^ 2)) :=
    (hre.pow 2).add (him.pow 2)
  rw [one_re, one_im, show (1 : ℝ) ^ 2 + (0 : ℝ) ^ 2 = 1 by norm_num] at hQ
  have := (hQ.log (by norm_num)).const_mul (1 / 2)
  rw [Real.log_one, mul_zero] at this
  exact this

lemma tendsto_H (χ : DirichletCharacter ℂ N) (x : ℕ) : Tendsto (H χ x) atTop (𝓝 0) := by
  have h1 := (continuous_re.tendsto 0).comp (tendsto_Acx χ x)
  have h2 := (tendsto_Bf χ).const_mul (Real.log x)
  have h3 := (continuous_re.tendsto 0).comp (tendsto_F χ)
  have := (h1.add h2).add h3
  rw [zero_re, mul_zero, add_zero, add_zero] at this
  exact this

/-! ### `H(1)` -/

lemma Acx_one (χ : DirichletCharacter ℂ N) (x : ℕ) (hx : 2 ≤ x) :
    Acx χ x ((1 : ℝ) : ℂ) = -(Real.log x : ℂ) * l1Sum χ x := by
  have hx1 : (1 : ℝ) < x := by exact_mod_cast hx
  have hlx : (Real.log x : ℂ) ≠ 0 := ofReal_ne_zero.2 (Real.log_pos hx1).ne'
  unfold Acx l1Sum
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [ofReal_one, cpow_neg_one]
  rcases lt_or_ge n 2 with hn | hn
  · simp [coef, vM_lt_two hn]
  · have hn1 : (1 : ℝ) < n := by exact_mod_cast hn
    have hln : (Real.log n : ℂ) ≠ 0 := ofReal_ne_zero.2 (Real.log_pos hn1).ne'
    have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
    have hln' : Complex.log (n : ℂ) ≠ 0 := by rw [← Complex.natCast_log]; exact hln
    have hlx' : Complex.log (x : ℂ) ≠ 0 := by rw [← Complex.natCast_log]; exact hlx
    unfold coef
    push_cast
    field_simp

end L1Int

open L1Int

variable {N : ℕ} [NeZero N]

/-- LLS Lemma 2.5 (Mathlib normalisation):
`|log |L(1,χ)| − Re l1Sum χ x + Re (L'/L)(1)/log x| ≤ (Z2/√x + 2/x)/(log x)²`. -/
theorem log_norm_L1_le (hGRH : DirichletLNonvanishingRightOfHalf) {χ : DirichletCharacter ℂ N}
    (hprim : χ.IsPrimitive) (hχ : χ ≠ 1) (x : ℕ) (hx : 2 ≤ x) :
    |Real.log ‖DirichletCharacter.LFunction χ 1‖ - (l1Sum χ x).re
        + (deriv (DirichletCharacter.LFunction χ) 1 / DirichletCharacter.LFunction χ 1).re
          / Real.log x|
      ≤ (Z2 χ / √(x : ℝ) + 2 / x) / Real.log x ^ 2 := by
  have hx1 : (1 : ℝ) < x := by exact_mod_cast hx
  have hx0 : (0 : ℝ) < x := by linarith
  have hlx : 0 < Real.log x := Real.log_pos hx1
  set Z := Z2 χ
  -- `|H'| ≤ P'` on `(1, ∞)`
  have hbound : ∀ σ : ℝ, 1 < σ →
      |(Hd χ x σ).re| ≤ (x : ℝ) ^ ((1 : ℝ) / 2 - σ) * Z + 2 * (x : ℝ) ^ (-σ) := fun σ hσ =>
    (abs_re_le_norm _).trans (shifted_log_bound hGRH hprim hχ x hx σ hσ)
  have hD : ∀ σ ∈ Ici (1 : ℝ), HasDerivAt (fun σ => H χ x σ + P x Z σ)
      ((Hd χ x σ).re + ((x : ℝ) ^ ((1 : ℝ) / 2 - σ) * Z + 2 * (x : ℝ) ^ (-σ))) σ :=
    fun σ hσ => (hasDerivAt_H hχ x hσ).add (hasDerivAt_P hx1 Z σ)
  have hD' : ∀ σ ∈ Ici (1 : ℝ), HasDerivAt (fun σ => P x Z σ - H χ x σ)
      (((x : ℝ) ^ ((1 : ℝ) / 2 - σ) * Z + 2 * (x : ℝ) ^ (-σ)) - (Hd χ x σ).re) σ :=
    fun σ hσ => (hasDerivAt_P hx1 Z σ).sub (hasDerivAt_H hχ x hσ)
  have hint : interior (Ici (1 : ℝ)) = Ioi 1 := interior_Ici
  have hmono1 : MonotoneOn (fun σ => H χ x σ + P x Z σ) (Ici 1) := by
    refine monotoneOn_of_deriv_nonneg (convex_Ici 1)
      (fun σ hσ => (hD σ hσ).continuousAt.continuousWithinAt) ?_ ?_
    · rw [hint]; exact fun σ hσ => (hD σ (Ioi_subset_Ici_self hσ)).differentiableAt.differentiableWithinAt
    · rw [hint]
      intro σ hσ
      rw [(hD σ (Ioi_subset_Ici_self hσ)).deriv]
      have := hbound σ hσ
      have := neg_abs_le (Hd χ x σ).re
      linarith
  have hmono2 : MonotoneOn (fun σ => P x Z σ - H χ x σ) (Ici 1) := by
    refine monotoneOn_of_deriv_nonneg (convex_Ici 1)
      (fun σ hσ => (hD' σ hσ).continuousAt.continuousWithinAt) ?_ ?_
    · rw [hint]; exact fun σ hσ => (hD' σ (Ioi_subset_Ici_self hσ)).differentiableAt.differentiableWithinAt
    · rw [hint]
      intro σ hσ
      rw [(hD' σ (Ioi_subset_Ici_self hσ)).deriv]
      have := hbound σ hσ
      have := le_abs_self (Hd χ x σ).re
      linarith
  have hlimH := tendsto_H χ x
  have hlimP := tendsto_P hx1 Z
  have hev : ∀ᶠ T in atTop, (1 : ℝ) ≤ T := eventually_ge_atTop 1
  have hA : H χ x 1 + P x Z 1 ≤ 0 := by
    have hl := hlimH.add hlimP
    rw [add_zero] at hl
    exact ge_of_tendsto hl (hev.mono fun T hT => hmono1 self_mem_Ici hT hT)
  have hB : P x Z 1 - H χ x 1 ≤ 0 := by
    have hl := hlimP.sub hlimH
    rw [sub_zero] at hl
    exact ge_of_tendsto hl (hev.mono fun T hT => hmono2 self_mem_Ici hT hT)
  -- identify `H(1)` and `P(1)`
  have hH1 : H χ x 1 = Real.log x * (Real.log ‖DirichletCharacter.LFunction χ 1‖
      - (l1Sum χ x).re
      + (deriv (DirichletCharacter.LFunction χ) 1 / DirichletCharacter.LFunction χ 1).re
        / Real.log x) := by
    unfold H
    rw [Acx_one χ x hx, Bf_eq]
    simp only [ofReal_one, neg_mul, neg_re, re_ofReal_mul, F]
    field_simp
    ring
  have hP1 : P x Z 1 = -((Z / √(x : ℝ) + 2 / x) / Real.log x) := by
    unfold P
    have e1 : (x : ℝ) ^ ((1 : ℝ) / 2 - 1) = 1 / √(x : ℝ) := by
      rw [show (1 : ℝ) / 2 - 1 = -(1 / 2) by norm_num, Real.rpow_neg hx0.le,
        Real.sqrt_eq_rpow, one_div]
      simp [one_div]
    have e2 : (x : ℝ) ^ (-(1 : ℝ)) = 1 / x := by rw [Real.rpow_neg_one, one_div]
    rw [e1, e2]
    ring
  rw [hH1, hP1] at hA hB
  set E := Real.log ‖DirichletCharacter.LFunction χ 1‖ - (l1Sum χ x).re
      + (deriv (DirichletCharacter.LFunction χ) 1 / DirichletCharacter.LFunction χ 1).re
        / Real.log x
  set R := (Z / √(x : ℝ) + 2 / x) / Real.log x with hR
  have eR : (Z / √(x : ℝ) + 2 / x) / Real.log x ^ 2 = R / Real.log x := by
    rw [hR, pow_two, div_div]
  rw [eR, abs_le]
  constructor
  · rw [← neg_div, div_le_iff₀ hlx]; linarith
  · rw [le_div_iff₀ hlx]; linarith

end LLS
