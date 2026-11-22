import Erdos985.Analytic.ExplicitFormula.Basic
import Erdos985.Analytic.XiGrowth

/-!
# Auxiliary facts for the explicit formula: zeros and term-by-term integration
-/

namespace Erdos985.Analytic.IdentityAux

open Complex MeasureTheory

/-- A function that is the pointwise sum of integrable functions with summable `L¹` norms
is integrable. -/
theorem integrable_of_hasSum {ι : Type*} [Countable ι] {F : ι → ℝ → ℂ} {f : ℝ → ℂ}
    (hf : AEStronglyMeasurable f) (hF_int : ∀ i, Integrable (F i))
    (hF_sum : Summable fun i => ∫ t, ‖F i t‖) (hsum : ∀ t, HasSum (fun i => F i t) (f t)) :
    Integrable f := by
  refine ⟨hf, ?_⟩
  have h1 : ∀ t, ‖f t‖ₑ ≤ ∑' i, ‖F i t‖ₑ := fun t => by
    rw [← (hsum t).tsum_eq]; exact eNorm_tsum_le_tsum_eNorm
  unfold HasFiniteIntegral
  calc ∫⁻ t, ‖f t‖ₑ ≤ ∫⁻ t, ∑' i, ‖F i t‖ₑ := lintegral_mono h1
    _ = ∑' i, ∫⁻ t, ‖F i t‖ₑ := lintegral_tsum fun i => (hF_int i).1.eNorm
    _ = ∑' i, ENNReal.ofReal (∫ t, ‖F i t‖) := by
        congr 1; funext i; rw [ofReal_integral_norm_eq_lintegral_eNorm (hF_int i)]
    _ = ENNReal.ofReal (∑' i, ∫ t, ‖F i t‖) :=
        (ENNReal.ofReal_tsum_of_nonneg (fun i => integral_nonneg fun _ => norm_nonneg _)
          hF_sum).symm
    _ < ⊤ := ENNReal.ofReal_lt_top

variable {N : ℕ} [NeZero N]

/-- Zeros of the completed L-function of a primitive nontrivial character lie in `0 < Re < 1`. -/
theorem zero_re_mem {χ : DirichletCharacter ℂ N} (hprim : χ.IsPrimitive) (hχ : χ ≠ 1) {ρ : ℂ}
    (hρ : DirichletCharacter.completedLFunction χ ρ = 0) : 0 < ρ.re ∧ ρ.re < 1 := by
  constructor
  · by_contra h
    push Not at h
    have h1 : DirichletCharacter.completedLFunction χ (1 - (1 - ρ)) ≠ 0 := by
      rw [hprim.completedLFunction_one_sub]
      refine mul_ne_zero (mul_ne_zero ?_ (DirichletCharacter.rootNumber_ne_zero hprim)) ?_
      · exact (cpow_ne_zero_iff_of_exponent_ne_zero (by
          intro h0; have := congrArg Complex.re h0; simp at this; linarith)).mpr
          (by exact_mod_cast NeZero.ne N)
      · exact DirichletCharacter.completedLFunction_ne_zero_of_one_le_re χ⁻¹
          (Or.inl (by simpa using hχ)) (by simp; linarith)
    exact h1 (by simpa using hρ)
  · by_contra h
    push Not at h
    exact DirichletCharacter.completedLFunction_ne_zero_of_one_le_re χ (Or.inl hχ) h hρ

/-- Every zero has positive multiplicity. -/
theorem order_ne_zero {χ : DirichletCharacter ℂ N} (hprim : χ.IsPrimitive) (hχ : χ ≠ 1) {ρ : ℂ}
    (hρ : DirichletCharacter.completedLFunction χ ρ = 0) :
    analyticOrderNatAt (DirichletCharacter.completedLFunction χ) ρ ≠ 0 := by
  have hd := DirichletCharacter.differentiable_completedLFunction hχ
  have han : AnalyticOnNhd ℂ (DirichletCharacter.completedLFunction χ) Set.univ :=
    hd.differentiableOn.analyticOnNhd isOpen_univ
  have h0 : analyticOrderAt (DirichletCharacter.completedLFunction χ) 0 ≠ ⊤ := by
    rw [(analyticOrderAt_eq_zero.2 (Or.inr (completedLFunction_zero_ne_zero χ hχ hprim)))]
    exact ENat.zero_ne_top
  have htop := han.analyticOrderAt_ne_top_of_isPreconnected isPreconnected_univ
    (Set.mem_univ 0) (Set.mem_univ ρ) h0
  intro hm
  have := Nat.cast_analyticOrderNatAt htop
  rw [hm, Nat.cast_zero, eq_comm, analyticOrderAt_eq_zero] at this
  rcases this with h | h
  · exact h (han ρ (Set.mem_univ _))
  · exact h hρ

/-- The zero set is countable. -/
theorem countable_zeros {χ : DirichletCharacter ℂ N} (hprim : χ.IsPrimitive) (hχ : χ ≠ 1) :
    Countable {ρ : ℂ // DirichletCharacter.completedLFunction χ ρ = 0} := by
  have hs := (hadamard_logDeriv (DirichletCharacter.differentiable_completedLFunction hχ)
    (completedLFunction_zero_ne_zero χ hχ hprim) (completedLFunction_growth χ hχ)).1 1 one_pos
  rw [← Set.countable_univ_iff]
  convert hs.countable_support
  symm
  rw [Function.support_eq_univ]
  intro ρ
  have hm := order_ne_zero hprim hχ ρ.2
  have hρ0 : (ρ : ℂ) ≠ 0 := fun h => (zero_re_mem hprim hχ ρ.2).1.ne' (by simp [h])
  have : 0 < ‖(ρ : ℂ)‖ := norm_pos_iff.2 hρ0
  positivity

end Erdos985.Analytic.IdentityAux
