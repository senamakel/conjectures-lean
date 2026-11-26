import Erdos985.Analytic.ExplicitFormula.StepA

/-!
# Logarithmic derivative of the functional equation, and the geometry of critical-line zeros
-/

namespace Erdos985.Analytic.ZeroSumAux

open Complex

variable {N : ℕ} [NeZero N]

/-- `−Λ'/Λ(1 − s, χ) = log N + Λ'/Λ(s, χ⁻¹)`. -/
theorem logDeriv_functional_equation {χ : DirichletCharacter ℂ N} (hprim : χ.IsPrimitive)
    (hχ : χ ≠ 1) {s : ℂ} (hs : DirichletCharacter.completedLFunction χ⁻¹ s ≠ 0) :
    -(deriv (DirichletCharacter.completedLFunction χ) (1 - s)
        / DirichletCharacter.completedLFunction χ (1 - s))
      = (Real.log N : ℂ) + deriv (DirichletCharacter.completedLFunction χ⁻¹) s
          / DirichletCharacter.completedLFunction χ⁻¹ s := by
  have hχi : χ⁻¹ ≠ 1 := by simpa using hχ
  have hN : (N : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne N
  have hF : HasDerivAt (fun w => DirichletCharacter.completedLFunction χ (1 - w))
      (deriv (DirichletCharacter.completedLFunction χ) (1 - s) * (-1)) s :=
    (DirichletCharacter.differentiable_completedLFunction hχ (1 - s)).hasDerivAt.comp s
      ((hasDerivAt_id s).const_sub 1)
  have hP : HasDerivAt (fun w : ℂ => (N : ℂ) ^ (w - 1 / 2))
      ((N : ℂ) ^ (s - 1 / 2) * Complex.log N * 1) s :=
    ((hasDerivAt_id s).sub_const (1 / 2)).const_cpow (Or.inl hN)
  have hG := (hP.mul_const (DirichletCharacter.rootNumber χ)).mul
    (DirichletCharacter.differentiable_completedLFunction hχi s).hasDerivAt
  have hfun : (fun w => DirichletCharacter.completedLFunction χ (1 - w))
      = fun w => (N : ℂ) ^ (w - 1 / 2) * DirichletCharacter.rootNumber χ
          * DirichletCharacter.completedLFunction χ⁻¹ w :=
    funext hprim.completedLFunction_one_sub
  rw [hfun] at hF
  have hd := hF.unique hG
  have hval := hprim.completedLFunction_one_sub s
  have hlog : Complex.log N = (Real.log N : ℂ) := by
    rw [Complex.ofReal_log (Nat.cast_nonneg N)]; simp
  have hPne : (N : ℂ) ^ (s - 1 / 2) ≠ 0 := by
    rw [Ne, cpow_eq_zero_iff]; exact fun h => hN h.1
  have hε := DirichletCharacter.rootNumber_ne_zero hprim
  rw [hval, ← hlog]
  have : deriv (DirichletCharacter.completedLFunction χ) (1 - s)
      = -((N : ℂ) ^ (s - 1 / 2) * Complex.log N * 1 * DirichletCharacter.rootNumber χ
          * DirichletCharacter.completedLFunction χ⁻¹ s
        + (N : ℂ) ^ (s - 1 / 2) * DirichletCharacter.rootNumber χ
          * deriv (DirichletCharacter.completedLFunction χ⁻¹) s) := by
    linear_combination (-1 : ℂ) * hd
  rw [this]
  generalize (N : ℂ) ^ (s - 1 / 2) = P at *
  field_simp

/-- For a zero on the critical line and real `x`, `Re 1/(1 − x − ρ) = −Re 1/(x − ρ)`. -/
theorem re_inv_reflect {ρ : ℂ} (hρ : ρ.re = 1 / 2) (x : ℝ) :
    (1 / ((1 : ℂ) - x - ρ)).re = -(1 / ((x : ℂ) - ρ)).re := by
  obtain ⟨a, b⟩ := ρ
  simp only at hρ
  subst hρ
  simp [normSq_apply]
  ring_nf

/-- For a zero on the critical line, `1/|ρ(ρ+1)| ≤ (4/3) Re 1/(3/2 − ρ)`. -/
theorem inv_norm_mul_le {ρ : ℂ} (hρ : ρ.re = 1 / 2) :
    1 / ‖ρ * (ρ + 1)‖ ≤ (4 / 3) * (1 / ((3 / 2 : ℂ) - ρ)).re := by
  obtain ⟨a, γ⟩ := ρ
  simp only at hρ
  subst hρ
  have hre : (1 / ((3 / 2 : ℂ) - ⟨1 / 2, γ⟩)).re = 1 / (1 + γ ^ 2) := by
    simp [normSq_apply]
    norm_num
    ring
  rw [hre]
  set t := ‖(⟨1 / 2, γ⟩ : ℂ) * (⟨1 / 2, γ⟩ + 1)‖ with ht
  have ht0 : 0 ≤ t := norm_nonneg _
  have hsq : t ^ 2 = (1 / 4 + γ ^ 2) * (9 / 4 + γ ^ 2) := by
    rw [ht, ← normSq_eq_norm_sq, normSq_mul]
    simp [normSq_apply]
    ring
  have hlow : (3 / 4) * (1 + γ ^ 2) ≤ t := by
    have h1 : ((3 / 4) * (1 + γ ^ 2)) ^ 2 ≤ t ^ 2 := by
      rw [hsq]; nlinarith [sq_nonneg γ]
    nlinarith [sq_nonneg γ]
  have hpos : 0 < (3 / 4) * (1 + γ ^ 2) := by positivity
  calc 1 / t ≤ 1 / ((3 / 4) * (1 + γ ^ 2)) := one_div_le_one_div_of_le hpos hlow
    _ = 4 / 3 * (1 / (1 + γ ^ 2)) := by field_simp

end Erdos985.Analytic.ZeroSumAux
