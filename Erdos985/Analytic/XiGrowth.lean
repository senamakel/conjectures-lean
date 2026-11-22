import Mathlib
import Erdos985.Analytic.XiOrder.Completed

/-!
# The completed L-functions are entire of order ≤ 1

`xiZeta s = s (s - 1) Λ(s)` (Riemann's ξ up to a factor ½), written via Mathlib's entire
`completedRiemannZeta₀`, and `completedLFunction χ` for non-trivial primitive `χ`.
-/

open Complex

namespace Erdos985.Analytic

/-- Riemann's `ξ`, up to the factor `1/2`: `s (s - 1) Λ(s)`, extended to an entire function. -/
noncomputable def xiZeta (s : ℂ) : ℂ := s * (s - 1) * completedRiemannZeta₀ s + 1

theorem differentiable_xiZeta : Differentiable ℂ xiZeta := by
  unfold xiZeta
  have := differentiable_completedZeta₀
  fun_prop

theorem xiZeta_eq {s : ℂ} (hs0 : s ≠ 0) (hs1 : s ≠ 1) :
    xiZeta s = s * (s - 1) * completedRiemannZeta s := by
  have h1 : (1 : ℂ) - s ≠ 0 := sub_ne_zero.mpr (Ne.symm hs1)
  have h2 : s - 1 ≠ 0 := sub_ne_zero.mpr hs1
  rw [xiZeta, completedRiemannZeta_eq]
  field_simp
  ring

theorem xiZeta_zero : xiZeta 0 = 1 := by simp [xiZeta]

open XiOrderAux in
/-- Bridge from the `LogGrowth` class of `XiOrder` to the bound
`C * exp (C * ‖s‖ * log (‖s‖ + 2))`. -/
theorem growth_of_logGrowth {F : ℂ → ℂ} (hF : LogGrowth F) :
    ∃ C : ℝ, ∀ s : ℂ, ‖F s‖ ≤ C * Real.exp (C * ‖s‖ * Real.log (‖s‖ + 2)) := by
  obtain ⟨K, a, b, ha, hb, h⟩ := hF
  have hK : 0 ≤ K := LogGrowth.nonneg_K h
  set lb := Real.log b
  have hlb : 0 ≤ lb := Real.log_nonneg (by linarith)
  set C₀ := a * (2 * lb + 1 + 2 * b)
  set D := a * (b * (lb + 1))
  refine ⟨max (K * Real.exp D) C₀, fun s => (h s).trans ?_⟩
  set u := ‖s‖
  have hu : 0 ≤ u := norm_nonneg s
  set ℓ := Real.log (u + 2)
  have hℓ2 : (1 / 2 : ℝ) ≤ ℓ := by
    have := Real.log_two_gt_d9
    have : Real.log 2 ≤ ℓ := Real.log_le_log (by norm_num) (by linarith)
    linarith
  have hℓu : ℓ ≤ u + 1 := by
    have := Real.log_le_sub_one_of_pos (show 0 < u + 2 by linarith); linarith
  have hL : 0 ≤ u * ℓ := by positivity
  have h1 : Real.log (u + b) ≤ lb + ℓ := by
    rw [← Real.log_mul (by linarith) (by linarith)]
    exact Real.log_le_log (by linarith) (by nlinarith)
  have h2 : u ≤ 2 * (u * ℓ) := by nlinarith
  have key : a * ((u + b) * Real.log (u + b)) ≤ C₀ * (u * ℓ) + D := by
    have e : (u + b) * Real.log (u + b) ≤ (2 * lb + 1 + 2 * b) * (u * ℓ) + b * (lb + 1) := by
      calc (u + b) * Real.log (u + b) ≤ (u + b) * (lb + ℓ) :=
            mul_le_mul_of_nonneg_left h1 (by linarith)
        _ = lb * u + u * ℓ + b * lb + b * ℓ := by ring
        _ ≤ lb * (2 * (u * ℓ)) + u * ℓ + b * lb + b * (2 * (u * ℓ) + 1) := by
            gcongr; linarith
        _ = _ := by ring
    have := mul_le_mul_of_nonneg_left e ha
    simp only [C₀, D]; nlinarith
  calc K * Real.exp (a * ((u + b) * Real.log (u + b)))
      ≤ K * Real.exp (C₀ * (u * ℓ) + D) := by gcongr
    _ = K * Real.exp D * Real.exp (C₀ * (u * ℓ)) := by
        rw [Real.exp_add]; ring
    _ ≤ max (K * Real.exp D) C₀ * Real.exp (max (K * Real.exp D) C₀ * (u * ℓ)) :=
        mul_le_mul (le_max_left _ _)
          (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (le_max_right _ _) hL))
          (Real.exp_pos _).le (le_max_of_le_left (by positivity))
    _ = _ := by ring_nf

theorem xiZeta_growth :
    ∃ C : ℝ, ∀ s : ℂ, ‖xiZeta s‖ ≤ C * Real.exp (C * ‖s‖ * Real.log (‖s‖ + 2)) := by
  open XiOrderAux in
  have hid : LogGrowth (fun s : ℂ => s) := by
    refine ⟨1, 1, 3, zero_le_one, le_rfl, fun s => ?_⟩
    have h3 : 1 ≤ Real.log (‖s‖ + 3) := one_le_log_of_three_le (by linarith [norm_nonneg s])
    have := Real.add_one_le_exp ‖s‖
    have : ‖s‖ ≤ (‖s‖ + 3) * Real.log (‖s‖ + 3) := by nlinarith [norm_nonneg s]
    have : Real.exp ‖s‖ ≤ Real.exp (1 * ((‖s‖ + 3) * Real.log (‖s‖ + 3))) :=
      Real.exp_le_exp.mpr (by linarith)
    linarith
  open XiOrderAux in
  have h : LogGrowth xiZeta :=
    (((hid.mul (hid.add (LogGrowth.const (-1)))).mul
      (completedHurwitzZetaEven₀_logGrowth 0)).add (LogGrowth.const 1)).congr fun s => by
        simp only [xiZeta, completedRiemannZeta₀]; ring
  exact growth_of_logGrowth h

theorem completedLFunction_growth {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) :
    ∃ C : ℝ, ∀ s : ℂ, ‖DirichletCharacter.completedLFunction χ s‖
      ≤ C * Real.exp (C * ‖s‖ * Real.log (‖s‖ + 2)) :=
  growth_of_logGrowth (XiOrderAux.completedLFunction_logGrowth hχ)

theorem completedLFunction_zero_ne_zero {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (hχ : χ ≠ 1) (hprim : χ.IsPrimitive) :
    DirichletCharacter.completedLFunction χ 0 ≠ 0 := by
  have h := hprim.completedLFunction_one_sub 1
  rw [sub_self] at h
  rw [h]
  refine mul_ne_zero (mul_ne_zero ?_ (DirichletCharacter.rootNumber_ne_zero hprim)) ?_
  · exact (cpow_ne_zero_iff_of_exponent_ne_zero (by norm_num)).mpr (by exact_mod_cast NeZero.ne N)
  · exact DirichletCharacter.completedLFunction_ne_zero_of_one_le_re χ⁻¹
      (Or.inl (by simpa using hχ)) (by simp)

end Erdos985.Analytic
