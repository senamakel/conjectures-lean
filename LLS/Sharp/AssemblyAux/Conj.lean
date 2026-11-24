import LLS.Sharp.Defs

/-!
# `Re D(1, χ⁻¹) = Re D(1, χ)`

`χ⁻¹(n) = conj χ(n)`, so `L(s, χ⁻¹) = conj L(conj s, χ)` on `Re s > 1`, hence everywhere by the
identity theorem; the derivative at `1` is the conjugate as well. The gamma factor depends only
on the parity, and `χ⁻¹` has the parity of `χ`.
-/

namespace LLS.Sharp.AssemblyAux

open Complex ComplexConjugate Erdos985.Analytic

variable {N : ℕ} [NeZero N]

omit [NeZero N] in
lemma parity_inv (χ : DirichletCharacter ℂ N) : parity χ⁻¹ = parity χ := by
  have h : χ⁻¹.Even ↔ χ.Even := by
    unfold DirichletCharacter.Even
    rw [MulChar.inv_apply_eq_inv', inv_eq_one]
  unfold parity
  by_cases hc : χ.Even
  · simp only [hc, h.mpr hc, ite_true]
  · simp only [hc, mt h.mp hc, ite_false]

omit [NeZero N] in
lemma gammaLogDeriv_inv (χ : DirichletCharacter ℂ N) (s : ℂ) :
    gammaLogDeriv χ⁻¹ s = gammaLogDeriv χ s := by
  unfold gammaLogDeriv; rw [parity_inv]

omit [NeZero N] in
lemma LSeries_inv_eq_conj (χ : DirichletCharacter ℂ N) (s : ℂ) :
    LSeries (fun n => χ⁻¹ n) s = conj (LSeries (fun n => χ n) (conj s)) := by
  unfold LSeries
  rw [Complex.conj_tsum]
  refine tsum_congr fun n => ?_
  simp only [LSeries.term_def]
  by_cases hn : n = 0
  · simp [hn]
  · simp only [hn, ite_false]
    rw [map_div₀]
    have harg : ((n : ℂ)).arg ≠ Real.pi := by
      rw [Complex.natCast_arg]; exact Real.pi_pos.ne
    have h1 : (n : ℂ) ^ conj s = conj ((n : ℂ) ^ s) := by
      rw [Complex.cpow_conj _ _ harg, Complex.conj_natCast]
    have h2 : χ⁻¹ (n : ZMod N) = conj (χ n) := by
      rw [← MulChar.star_apply']; rfl
    rw [h1, Complex.conj_conj, h2]

lemma LFunction_inv_eq_conj {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1) :
    DirichletCharacter.LFunction χ⁻¹ =
      conj ∘ DirichletCharacter.LFunction χ ∘ conj := by
  have hχi : χ⁻¹ ≠ 1 := by simpa using hχ
  have hg : Differentiable ℂ (conj ∘ DirichletCharacter.LFunction χ ∘ conj) := by
    intro z
    have := ((DirichletCharacter.differentiable_LFunction hχ) (conj z)).conj_conj
    rwa [Complex.conj_conj] at this
  refine AnalyticOnNhd.eq_of_eventuallyEq (z₀ := 2)
    (fun z _ => (DirichletCharacter.differentiable_LFunction hχi).analyticAt z)
    (fun z _ => hg.analyticAt z) ?_
  filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds
    (show (2 : ℂ) ∈ {w : ℂ | 1 < w.re} by norm_num)] with w hw
  have hw' : 1 < (conj w).re := by simpa using hw
  simp only [Function.comp_apply]
  rw [DirichletCharacter.LFunction_eq_LSeries _ hw, DirichletCharacter.LFunction_eq_LSeries _ hw',
    LSeries_inv_eq_conj]

lemma re_logDeriv_LFunction_inv {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1) :
    (deriv (DirichletCharacter.LFunction χ⁻¹) 1 / DirichletCharacter.LFunction χ⁻¹ 1).re
      = (deriv (DirichletCharacter.LFunction χ) 1 / DirichletCharacter.LFunction χ 1).re := by
  have hd : HasDerivAt (conj ∘ DirichletCharacter.LFunction χ ∘ conj)
      (conj (deriv (DirichletCharacter.LFunction χ) 1)) 1 := by
    have := ((DirichletCharacter.differentiable_LFunction hχ) 1).hasDerivAt.conj_conj
    rwa [map_one] at this
  rw [LFunction_inv_eq_conj hχ, hd.deriv]
  simp only [Function.comp_apply, map_one]
  rw [← map_div₀, Complex.conj_re]

/-- `Re D(1, χ⁻¹) = Re D(1, χ)` for `χ ≠ 1`. -/
theorem re_D_inv_one {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1) :
    (LLS.D χ⁻¹ 1).re = (LLS.D χ 1).re := by
  have hχi : χ⁻¹ ≠ 1 := by simpa using hχ
  rw [LLS.D_one_eq hχ, LLS.D_one_eq hχi, add_re, add_re, gammaLogDeriv_inv,
    re_logDeriv_LFunction_inv hχ]

end LLS.Sharp.AssemblyAux
