import Lindelof.Main
import Erdos985.Analytic.ExplicitFormula.StepA
import Erdos985.Analytic.XiGrowth

/-!
# Dirichlet Step 2: `|Λ(s, χ)|` almost increases to the right of the critical line

For a primitive character `χ ≠ 1` mod `N`, `Λ(s, χ) = completedLFunction χ s` is entire of order
one with `Λ(0, χ) ≠ 0` (erdos-985). Under GRH all its zeros lie on `Re s = 1/2`
(`Erdos985.Analytic.completedLFunction_zero_re`).

* `completedLFunction_conj`: `conj Λ(s̄, χ) = Λ(s, χ⁻¹)` (identity theorem from `Re s > 1`).
* `logDeriv_completedLFunction_one_sub_conj`: with the functional equation,
  `Λ'/Λ(1 - z̄, χ) = -log N - conj (Λ'/Λ(z, χ))`.
* `norm_completedLFunction_le`: under GRH, for `1/2 ≤ σ ≤ σ'`,
  `‖Λ(σ + it, χ)‖ ≤ N^{(σ' - σ)/2} ‖Λ(σ' + it, χ)‖`
  (generic Step 2, `norm_le_of_re_logDeriv_ge`, with `c = log N`).
-/

namespace Lindelof

open Complex ComplexConjugate Erdos985 Erdos985.Analytic DirichletCharacter Filter Topology

variable {N : ℕ} [NeZero N]

/-- `conj (χ a) = χ⁻¹ a` for a complex Dirichlet character. -/
lemma dirichlet_conj_apply (χ : DirichletCharacter ℂ N) (a : ZMod N) :
    conj (χ a) = χ⁻¹ a := by
  simpa using MulChar.star_apply' χ a

lemma dirichlet_even_inv_iff (χ : DirichletCharacter ℂ N) : (χ⁻¹).Even ↔ χ.Even := by
  unfold DirichletCharacter.Even
  rw [← dirichlet_conj_apply]
  constructor
  · intro h
    have := congrArg conj h
    simpa using this
  · intro h; rw [h, map_one]

lemma gammaFactor_inv (χ : DirichletCharacter ℂ N) (s : ℂ) :
    gammaFactor χ⁻¹ s = gammaFactor χ s := by
  rcases χ.even_or_odd with h | h
  · rw [h.gammaFactor_def, ((dirichlet_even_inv_iff χ).mpr h).gammaFactor_def]
  · rcases (χ⁻¹).even_or_odd with h' | h'
    · exfalso
      have he : χ.Even := (dirichlet_even_inv_iff χ).mp h'
      unfold DirichletCharacter.Even at he
      unfold DirichletCharacter.Odd at h
      rw [h] at he
      norm_num at he
    · rw [h.gammaFactor_def, h'.gammaFactor_def]

lemma gammaFactor_conj (χ : DirichletCharacter ℂ N) (s : ℂ) :
    conj (gammaFactor χ (conj s)) = gammaFactor χ s := by
  rcases χ.even_or_odd with h | h
  · rw [h.gammaFactor_def, h.gammaFactor_def, Gammaℝ_conj, conj_conj]
  · rw [h.gammaFactor_def, h.gammaFactor_def, show conj s + 1 = conj (s + 1) by simp,
      Gammaℝ_conj, conj_conj]

/-- `Λ(s, χ) = γ(s) L(s, χ)` for `Re s > 0`. -/
lemma completedLFunction_eq_mul (χ : DirichletCharacter ℂ N) {s : ℂ} (hs : 0 < s.re) :
    completedLFunction χ s = gammaFactor χ s * LFunction χ s := by
  rw [LFunction_eq_completed_div_gammaFactor χ s (Or.inl fun h => by simp [h] at hs),
    mul_div_cancel₀ _ (StepAAux.gammaFactor_ne_zero χ hs)]

lemma conj_LSeries (χ : DirichletCharacter ℂ N) (s : ℂ) :
    conj (LSeries (fun n => χ n) (conj s)) = LSeries (fun n => χ⁻¹ n) s := by
  rw [LSeries, LSeries, conj_tsum]
  refine tsum_congr fun n => ?_
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  · rw [LSeries.term_of_ne_zero hn, LSeries.term_of_ne_zero hn, map_div₀,
      ← conj_cpow _ _ (by rw [natCast_arg]; positivity), conj_natCast, dirichlet_conj_apply]

/-- **Conjugation symmetry**: `conj Λ(s̄, χ) = Λ(s, χ⁻¹)` for `χ ≠ 1`. -/
theorem completedLFunction_conj {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1) (s : ℂ) :
    conj (completedLFunction χ (conj s)) = completedLFunction χ⁻¹ s := by
  have hχ' : χ⁻¹ ≠ 1 := by simpa using hχ
  have hd := differentiable_completedLFunction hχ
  have hg : Differentiable ℂ (conj ∘ completedLFunction χ ∘ conj) := fun z =>
    differentiableAt_conj_conj_iff.mpr (hd _)
  have hfg : (conj ∘ completedLFunction χ ∘ conj) = completedLFunction χ⁻¹ := by
    refine AnalyticOnNhd.eq_of_eventuallyEq (z₀ := 2)
      (hg.differentiableOn.analyticOnNhd isOpen_univ)
      ((differentiable_completedLFunction hχ').differentiableOn.analyticOnNhd isOpen_univ) ?_
    refine eventually_of_mem
      ((isOpen_lt continuous_const continuous_re : IsOpen {b : ℂ | (1 : ℝ) < b.re}).mem_nhds
        (show (2 : ℂ) ∈ {b : ℂ | (1 : ℝ) < b.re} by simp)) fun z hz => ?_
    have hz : 1 < z.re := hz
    have hz0 : 0 < z.re := by linarith
    have hcz : 1 < (conj z).re := by rwa [conj_re]
    simp only [Function.comp]
    rw [completedLFunction_eq_mul χ (by linarith), completedLFunction_eq_mul χ⁻¹ hz0,
      LFunction_eq_LSeries χ hcz, LFunction_eq_LSeries χ⁻¹ hz, map_mul, gammaFactor_conj,
      gammaFactor_inv, conj_LSeries]
  have := congrFun hfg s
  simpa using this

/-- The derivative version of `completedLFunction_conj`. -/
theorem deriv_completedLFunction_conj {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1) (s : ℂ) :
    deriv (completedLFunction χ⁻¹) (conj s) = conj (deriv (completedLFunction χ) s) := by
  have hfun : (conj ∘ completedLFunction χ ∘ conj) = completedLFunction χ⁻¹ := by
    funext z; simp [Function.comp, completedLFunction_conj hχ]
  have h := congrFun (deriv_conj_conj (f := completedLFunction χ)) (conj s)
  rw [hfun] at h
  rw [h, Function.comp_apply, Function.comp_apply, conj_conj]

/-- With the functional equation: `Λ'/Λ(1 - z̄, χ) = -log N - conj (Λ'/Λ(z, χ))`. -/
theorem logDeriv_completedLFunction_one_sub_conj {χ : DirichletCharacter ℂ N}
    (hprim : χ.IsPrimitive) (hχ : χ ≠ 1) {z : ℂ}
    (hw : completedLFunction χ (1 - conj z) ≠ 0) :
    deriv (completedLFunction χ) (1 - conj z) / completedLFunction χ (1 - conj z) =
      -(Real.log N : ℂ) - conj (deriv (completedLFunction χ) z / completedLFunction χ z) := by
  have hχ' : χ⁻¹ ≠ 1 := by simpa using hχ
  have hN0 : (N : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne N
  have hFE : (fun v => completedLFunction χ (1 - v)) =
      fun v => (N : ℂ) ^ (v - 1 / 2) * rootNumber χ * completedLFunction χ⁻¹ v :=
    funext fun v => hprim.completedLFunction_one_sub v
  have h1 : HasDerivAt (fun v => completedLFunction χ (1 - v))
      (deriv (completedLFunction χ) (1 - conj z) * (-1)) (conj z) :=
    ((differentiable_completedLFunction hχ) (1 - conj z)).hasDerivAt.comp (conj z)
      ((hasDerivAt_id (conj z)).const_sub 1)
  have hpow : HasDerivAt (fun v => (N : ℂ) ^ (v - 1 / 2))
      ((N : ℂ) ^ (conj z - 1 / 2) * Complex.log N * 1) (conj z) :=
    ((hasDerivAt_id (conj z)).sub_const (1 / 2 : ℂ)).const_cpow (Or.inl hN0)
  have h2 : HasDerivAt (fun v => (N : ℂ) ^ (v - 1 / 2) * rootNumber χ * completedLFunction χ⁻¹ v)
      ((N : ℂ) ^ (conj z - 1 / 2) * Complex.log N * 1 * rootNumber χ *
          completedLFunction χ⁻¹ (conj z) +
        (N : ℂ) ^ (conj z - 1 / 2) * rootNumber χ * deriv (completedLFunction χ⁻¹) (conj z))
      (conj z) :=
    (hpow.mul_const _).mul ((differentiable_completedLFunction hχ') (conj z)).hasDerivAt
  rw [hFE] at h1
  have hd := h1.unique h2
  have hval := hprim.completedLFunction_one_sub (conj z)
  have hΛ'u : completedLFunction χ⁻¹ (conj z) = conj (completedLFunction χ z) := by
    rw [← completedLFunction_conj hχ, conj_conj]
  have hdΛ'u := deriv_completedLFunction_conj hχ z
  have hlog : Complex.log (N : ℂ) = (Real.log N : ℂ) := natCast_log.symm
  rw [hΛ'u, hdΛ'u, hlog] at hd
  rw [hΛ'u] at hval
  rw [hval] at hw ⊢
  have hdiv : deriv (completedLFunction χ) (1 - conj z) =
      -((N : ℂ) ^ (conj z - 1 / 2) * (Real.log N : ℂ) * 1 * rootNumber χ *
          conj (completedLFunction χ z) +
        (N : ℂ) ^ (conj z - 1 / 2) * rootNumber χ * conj (deriv (completedLFunction χ) z)) := by
    linear_combination -hd
  rw [hdiv, map_div₀]
  have hΛ0 : conj (completedLFunction χ z) ≠ 0 := by
    intro h; apply hw; rw [h, mul_zero]
  have hc : (N : ℂ) ^ (conj z - 1 / 2) * rootNumber χ ≠ 0 := by
    intro h; apply hw; rw [h, zero_mul]
  have hc1 : (N : ℂ) ^ (conj z - 1 / 2) ≠ 0 := left_ne_zero_of_mul hc
  have hc2 : rootNumber χ ≠ 0 := right_ne_zero_of_mul hc
  rw [div_eq_iff (mul_ne_zero hc hΛ0)]
  field_simp
  ring

/-- Under GRH, every zero of `Λ(·, χ)` (primitive `χ ≠ 1`) lies on `Re s = 1/2`. -/
theorem completedLFunction_ne_zero_of_GRH (hGRH : DirichletLNonvanishingRightOfHalf)
    {χ : DirichletCharacter ℂ N} (hprim : χ.IsPrimitive) (hχ : χ ≠ 1) {s : ℂ}
    (hs : s.re ≠ 1 / 2) : completedLFunction χ s ≠ 0 := fun h =>
  hs (completedLFunction_zero_re hGRH hprim hχ h)

/-- Under GRH, `2 Re Λ'/Λ(z, χ) ≥ -log N` for `Re z > 1/2`. -/
theorem re_logDeriv_completedLFunction_ge (hGRH : DirichletLNonvanishingRightOfHalf)
    {χ : DirichletCharacter ℂ N} (hprim : χ.IsPrimitive) (hχ : χ ≠ 1) {z : ℂ}
    (hz : 1 / 2 < z.re) :
    -Real.log N ≤ 2 * (deriv (completedLFunction χ) z / completedLFunction χ z).re := by
  have h := re_logDeriv_one_sub_conj_le (differentiable_completedLFunction hχ)
    (completedLFunction_zero_ne_zero χ hχ hprim) (completedLFunction_growth χ hχ)
    (fun ρ hρ => completedLFunction_zero_re hGRH hprim hχ hρ) hz
  have hw : completedLFunction χ (1 - conj z) ≠ 0 :=
    completedLFunction_ne_zero_of_GRH hGRH hprim hχ (by simp; linarith)
  rw [logDeriv_completedLFunction_one_sub_conj hprim hχ hw, sub_re, neg_re, ofReal_re,
    conj_re] at h
  linarith

/-- **Dirichlet Step 2.** Under GRH, for `1/2 ≤ σ ≤ σ'`,
`‖Λ(σ + it, χ)‖ ≤ e^{(log N)(σ' - σ)/2} ‖Λ(σ' + it, χ)‖`. -/
theorem norm_completedLFunction_le (hGRH : DirichletLNonvanishingRightOfHalf)
    {χ : DirichletCharacter ℂ N} (hprim : χ.IsPrimitive) (hχ : χ ≠ 1) (t : ℝ) {σ σ' : ℝ}
    (hσ : 1 / 2 ≤ σ) (hσσ' : σ ≤ σ') :
    ‖completedLFunction χ (σ + t * I)‖ ≤
      Real.exp (Real.log N * (σ' - σ) / 2) * ‖completedLFunction χ (σ' + t * I)‖ :=
  norm_le_of_re_logDeriv_ge (differentiable_completedLFunction hχ) (Real.log N)
    (fun z hz => completedLFunction_ne_zero_of_GRH hGRH hprim hχ (by linarith))
    (fun z hz => re_logDeriv_completedLFunction_ge hGRH hprim hχ hz) t hσ hσσ'

end Lindelof
