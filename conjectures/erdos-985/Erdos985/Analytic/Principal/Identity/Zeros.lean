import Erdos985.Analytic.ExplicitFormula.StepA
import Erdos985.Analytic.ExplicitFormula.Identity.Zeros
import Erdos985.Analytic.XiGrowth

/-!
# Zeros and logarithmic derivative of `ξ = xiZeta`
-/

namespace Erdos985.Analytic.PrincipalAux

open Complex

/-- `Λ(s) ≠ 0` for `Re s ≥ 1`. -/
theorem completedRiemannZeta_ne_zero_of_one_le_re {s : ℂ} (hs : 1 ≤ s.re) :
    completedRiemannZeta s ≠ 0 := by
  have hs0 : s ≠ 0 := fun h => by rw [h] at hs; simp at hs; linarith
  intro h
  apply riemannZeta_ne_zero_of_one_le_re hs
  rw [riemannZeta_def_of_ne_zero hs0, h, zero_div]

theorem xiZeta_one : xiZeta 1 = 1 := by simp [xiZeta]

theorem xiZeta_zero_re_mem {ρ : ℂ} (hρ : xiZeta ρ = 0) : 0 < ρ.re ∧ ρ.re < 1 := by
  have hρ0 : ρ ≠ 0 := fun h => by rw [h, xiZeta_zero] at hρ; exact one_ne_zero hρ
  have hρ1 : ρ ≠ 1 := fun h => by rw [h, xiZeta_one] at hρ; exact one_ne_zero hρ
  have hΛ : completedRiemannZeta ρ = 0 := by
    rw [xiZeta_eq hρ0 hρ1] at hρ
    rcases mul_eq_zero.mp hρ with h | h
    · rcases mul_eq_zero.mp h with h | h
      · exact absurd h hρ0
      · exact absurd (sub_eq_zero.mp h) hρ1
    · exact h
  constructor
  · by_contra h
    push Not at h
    apply completedRiemannZeta_ne_zero_of_one_le_re (s := 1 - ρ) (by simp; linarith)
    rw [completedRiemannZeta_one_sub, hΛ]
  · by_contra h
    push Not at h
    exact completedRiemannZeta_ne_zero_of_one_le_re h hΛ

/-- Every zero of `ξ` has positive multiplicity. -/
theorem xiZeta_order_ne_zero {ρ : ℂ} (hρ : xiZeta ρ = 0) : analyticOrderNatAt xiZeta ρ ≠ 0 := by
  have han : AnalyticOnNhd ℂ xiZeta Set.univ :=
    differentiable_xiZeta.differentiableOn.analyticOnNhd isOpen_univ
  have h0 : analyticOrderAt xiZeta 0 ≠ ⊤ := by
    rw [(analyticOrderAt_eq_zero.2 (Or.inr (by rw [xiZeta_zero]; exact one_ne_zero)))]
    exact ENat.zero_ne_top
  have htop := han.analyticOrderAt_ne_top_of_isPreconnected isPreconnected_univ
    (Set.mem_univ 0) (Set.mem_univ ρ) h0
  intro hm
  have := Nat.cast_analyticOrderNatAt htop
  rw [hm, Nat.cast_zero, eq_comm, analyticOrderAt_eq_zero] at this
  rcases this with h | h
  · exact h (han ρ (Set.mem_univ _))
  · exact h hρ

/-- The zero set of `ξ` is countable. -/
theorem countable_xiZeta_zeros : Countable {ρ : ℂ // xiZeta ρ = 0} := by
  have hs := (hadamard_logDeriv differentiable_xiZeta (by rw [xiZeta_zero]; exact one_ne_zero)
    xiZeta_growth).1 1 one_pos
  rw [← Set.countable_univ_iff]
  convert hs.countable_support
  symm
  rw [Function.support_eq_univ]
  intro ρ
  have hm := xiZeta_order_ne_zero ρ.2
  have hρ0 : (ρ : ℂ) ≠ 0 := fun h => (xiZeta_zero_re_mem ρ.2).1.ne' (by simp [h])
  have : 0 < ‖(ρ : ℂ)‖ := norm_pos_iff.2 hρ0
  positivity

theorem gammaLogDeriv_one (s : ℂ) :
    gammaLogDeriv (1 : DirichletCharacter ℂ 1) s
      = -(1 / 2) * (Real.log Real.pi : ℂ) + (1 / 2) * digamma (s / 2) := by
  simp [gammaLogDeriv, parity]

/-- `ζ'/ζ = ξ'/ξ − 1/s − 1/(s−1) − G` to the right of `Re s = 1`. -/
theorem logDeriv_riemannZeta_eq {s : ℂ} (hs : 1 < s.re) :
    deriv riemannZeta s / riemannZeta s
      = deriv xiZeta s / xiZeta s - 1 / s - 1 / (s - 1)
          - gammaLogDeriv (1 : DirichletCharacter ℂ 1) s := by
  have hs0 : 0 < s.re := by linarith
  have hne0 : s ≠ 0 := fun h => by rw [h] at hs; simp at hs; linarith
  have hne1 : s ≠ 1 := fun h => by rw [h] at hs; simp at hs
  have hne1' : s - 1 ≠ 0 := sub_ne_zero.mpr hne1
  have hζ : riemannZeta s ≠ 0 := riemannZeta_ne_zero_of_one_le_re hs.le
  have hγ : Gammaℝ s ≠ 0 := Gammaℝ_ne_zero_of_re_pos hs0
  have hev : xiZeta =ᶠ[nhds s] fun w => w * (w - 1) * (Gammaℝ w * riemannZeta w) := by
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds
      (show s ∈ {w : ℂ | 1 < w.re} from hs)] with w hw
    have hw0 : w ≠ 0 := fun h => by rw [h] at hw; simp at hw; linarith
    have hw1 : w ≠ 1 := fun h => by rw [h] at hw; simp at hw
    rw [xiZeta_eq hw0 hw1, riemannZeta_def_of_ne_zero hw0,
      mul_div_cancel₀ _ (Gammaℝ_ne_zero_of_re_pos (by linarith))]
  have hp : HasDerivAt (fun w : ℂ => w * (w - 1)) (1 * (s - 1) + s * 1) s :=
    (hasDerivAt_id s).mul ((hasDerivAt_id s).sub_const 1)
  have hd := hp.fun_mul ((StepAAux.hasDerivAt_Gammaℝ hs0).fun_mul
    (differentiableAt_riemannZeta hne1).hasDerivAt)
  rw [hev.deriv_eq, hd.deriv, hev.eq_of_nhds, gammaLogDeriv_one]
  field_simp
  ring

end Erdos985.Analytic.PrincipalAux
