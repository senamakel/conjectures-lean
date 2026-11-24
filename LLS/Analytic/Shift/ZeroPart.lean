import LLS.Analytic.Shift.Identity

/-!
# The zero part of the shifted Cesàro formula, under GRH

`Σ_ρ m_ρ zeroTerm x (ρ − 1) = (D(3) − D(1)) − (D(3) − D(0))/x − Z` with
`Z = Σ_ρ m_ρ x^{ρ−1}/((ρ−1)ρ)` and `|Z| ≤ Σ_ρ m_ρ/|ρ|² / √x`, by Hadamard at `3`, `1`, `0`.
-/

namespace LLS.ShiftAux

open Complex Erdos985 Erdos985.Analytic Erdos985.Analytic.IdentityAux

variable {N : ℕ} [NeZero N]

/-- Under GRH, `Σ_ρ m_ρ/|ρ|²` converges. -/
theorem summable_Z2 (hGRH : DirichletLNonvanishingRightOfHalf) {χ : DirichletCharacter ℂ N}
    (hprim : χ.IsPrimitive) (hχ : χ ≠ 1) :
    Summable (fun ρ : {ρ : ℂ // DirichletCharacter.completedLFunction χ ρ = 0} =>
        (analyticOrderNatAt (DirichletCharacter.completedLFunction χ) ρ : ℝ) / ‖(ρ : ℂ)‖ ^ 2) := by
  obtain ⟨hsum_ε, -⟩ := hadamard_logDeriv (DirichletCharacter.differentiable_completedLFunction hχ)
    (completedLFunction_zero_ne_zero χ hχ hprim) (completedLFunction_growth χ hχ)
  refine Summable.of_nonneg_of_le (fun _ => by positivity) (fun ρ => ?_)
    ((hsum_ε (1 / 2) (by norm_num)).mul_left 2)
  have hre := completedLFunction_zero_re hGRH hprim hχ ρ.2
  have hn : (1 / 2 : ℝ) ≤ ‖(ρ : ℂ)‖ := by
    have := Complex.abs_re_le_norm (ρ : ℂ); rw [hre] at this; norm_num at this ⊢; linarith
  have hn0 : 0 < ‖(ρ : ℂ)‖ := by linarith
  have hsq : (1 / 2 : ℝ) ≤ ‖(ρ : ℂ)‖ ^ (1 / 2 : ℝ) := by
    calc (1 / 2 : ℝ) = (1 / 4 : ℝ) ^ (1 / 2 : ℝ) := by
          rw [show (1 / 4 : ℝ) = (1 / 2) ^ (2 : ℝ) by norm_num, ← Real.rpow_mul (by norm_num)]
          norm_num
      _ ≤ _ := Real.rpow_le_rpow (by norm_num) (by linarith) (by norm_num)
  have e : ‖(ρ : ℂ)‖ ^ 2 = ‖(ρ : ℂ)‖ ^ (1 + 1 / 2 : ℝ) * ‖(ρ : ℂ)‖ ^ (1 / 2 : ℝ) := by
    rw [← Real.rpow_add hn0, show (1 + 1 / 2 + 1 / 2 : ℝ) = (2 : ℕ) by norm_num,
      Real.rpow_natCast]
  have hp : 0 < ‖(ρ : ℂ)‖ ^ (1 + 1 / 2 : ℝ) := by positivity
  have hm : (0 : ℝ) ≤ analyticOrderNatAt (DirichletCharacter.completedLFunction χ) ρ :=
    Nat.cast_nonneg _
  rw [e, div_le_iff₀ (by positivity)]
  calc (analyticOrderNatAt (DirichletCharacter.completedLFunction χ) ρ : ℝ)
      = 2 * ((analyticOrderNatAt (DirichletCharacter.completedLFunction χ) ρ : ℝ)
          / ‖(ρ : ℂ)‖ ^ (1 + 1 / 2 : ℝ)) * (‖(ρ : ℂ)‖ ^ (1 + 1 / 2 : ℝ) * (1 / 2)) := by
        field_simp
    _ ≤ 2 * ((analyticOrderNatAt (DirichletCharacter.completedLFunction χ) ρ : ℝ)
          / ‖(ρ : ℂ)‖ ^ (1 + 1 / 2 : ℝ)) * (‖(ρ : ℂ)‖ ^ (1 + 1 / 2 : ℝ)
            * ‖(ρ : ℂ)‖ ^ (1 / 2 : ℝ)) := by gcongr

theorem zeroPart_eq (hGRH : DirichletLNonvanishingRightOfHalf) {χ : DirichletCharacter ℂ N}
    (hprim : χ.IsPrimitive) (hχ : χ ≠ 1) (x : ℕ) (hx : 1 ≤ x) :
    ∃ Z : ℂ, ‖Z‖ ≤ Z2 χ / √(x : ℝ) ∧
      ∑' ρ : {ρ : ℂ // DirichletCharacter.completedLFunction χ ρ = 0},
          (analyticOrderNatAt (DirichletCharacter.completedLFunction χ) ρ : ℂ)
            * zeroTerm x ((ρ : ℂ) - 1)
        = (D χ 3 - D χ 1) - (D χ 3 - D χ 0) / x - Z := by
  set Λf := DirichletCharacter.completedLFunction χ with hΛf
  set m : {ρ : ℂ // Λf ρ = 0} → ℂ := fun ρ => (analyticOrderNatAt Λf ρ : ℂ) with hm
  have hx0 : (0 : ℝ) < x := by exact_mod_cast hx
  have hxC : (x : ℂ) ≠ 0 := by exact_mod_cast hx0.ne'
  obtain ⟨-, b, hb⟩ := hadamard_logDeriv (DirichletCharacter.differentiable_completedLFunction hχ)
    (completedLFunction_zero_ne_zero χ hχ hprim) (completedLFunction_growth χ hχ)
  have hΛne : ∀ z : ℂ, 1 ≤ z.re → Λf z ≠ 0 := fun z hz =>
    DirichletCharacter.completedLFunction_ne_zero_of_one_le_re χ (Or.inl hχ) hz
  have hH : ∀ z : ℂ, Λf z ≠ 0 →
      HasSum (fun ρ : {ρ : ℂ // Λf ρ = 0} => m ρ * (1 / (z - ρ) + 1 / ρ)) (D χ z - b) := by
    intro z hz
    obtain ⟨hs, he⟩ := hb z hz
    have : D χ z - b = ∑' ρ : {ρ : ℂ // Λf ρ = 0}, m ρ * (1 / (z - ρ) + 1 / ρ) := by
      unfold D; rw [he]; ring
    rw [this]; exact hs.hasSum
  have h3 := hH 3 (hΛne _ (by norm_num))
  have h1 := hH 1 (hΛne _ (by norm_num))
  have h0 := hH 0 (completedLFunction_zero_ne_zero χ hχ hprim)
  have hb0 : D χ 0 - b = 0 := by
    rw [← h0.tsum_eq]
    simp
  have hzre : ∀ ρ : {ρ : ℂ // Λf ρ = 0}, 0 < (ρ : ℂ).re ∧ (ρ : ℂ).re < 1 :=
    fun ρ => zero_re_mem hprim hχ ρ.2
  have hcrit : ∀ ρ : {ρ : ℂ // Λf ρ = 0}, (ρ : ℂ).re = 1 / 2 :=
    fun ρ => completedLFunction_zero_re hGRH hprim hχ ρ.2
  set Zt : {ρ : ℂ // Λf ρ = 0} → ℂ := fun ρ =>
    m ρ * ((x : ℂ) ^ ((ρ : ℂ) - 1) / (((ρ : ℂ) - 1) * ρ)) with hZt
  have hZn : ∀ ρ, ‖Zt ρ‖ = (analyticOrderNatAt Λf ρ : ℝ) / ‖(ρ : ℂ)‖ ^ 2 / √(x : ℝ) := by
    intro ρ
    simp only [Zt, m, norm_mul, norm_div, Complex.norm_natCast,
      Complex.norm_natCast_cpow_of_pos (show 0 < x by omega), sub_re, one_re, hcrit ρ,
      norm_sub_one_eq (hcrit ρ)]
    rw [show (1 / 2 - 1 : ℝ) = -(1 / 2) by norm_num, Real.rpow_neg hx0.le,
      ← Real.sqrt_eq_rpow]
    field_simp
  have hZs : Summable Zt := by
    refine Summable.of_norm ?_
    simp_rw [hZn]
    exact (summable_Z2 hGRH hprim hχ).div_const _
  refine ⟨∑' ρ, Zt ρ, ?_, ?_⟩
  · calc ‖∑' ρ, Zt ρ‖ ≤ ∑' ρ, ‖Zt ρ‖ := norm_tsum_le_tsum_norm hZs.norm
      _ = Z2 χ / √(x : ℝ) := by
        simp_rw [hZn]
        rw [tsum_div_const]
        rfl
  · have hterm : ∀ ρ : {ρ : ℂ // Λf ρ = 0}, m ρ * zeroTerm x ((ρ : ℂ) - 1)
        = m ρ * (1 / (3 - ρ) + 1 / ρ) - m ρ * (1 / (1 - ρ) + 1 / ρ)
          - 1 / (x : ℂ) * (m ρ * (1 / (3 - ρ) + 1 / ρ)) - Zt ρ := by
      intro ρ
      have hr0 : (ρ : ℂ) ≠ 0 := fun h => by have := hzre ρ; rw [h] at this; simp at this
      have hr1 : (ρ : ℂ) - 1 ≠ 0 := fun h => by
        have := congrArg Complex.re h; simp at this; linarith [hzre ρ]
      have hr1' : (1 : ℂ) - ρ ≠ 0 := fun h => by
        have := congrArg Complex.re h; simp at this; linarith [hzre ρ]
      have hr3 : (3 : ℂ) - ρ ≠ 0 := fun h => by
        have := congrArg Complex.re h; simp at this; linarith [hzre ρ]
      have hr2 : (2 : ℂ) - ((ρ : ℂ) - 1) ≠ 0 := fun h => by
        have := congrArg Complex.re h; simp at this; linarith [hzre ρ]
      have hr4 : (ρ : ℂ) - 1 + 1 ≠ 0 := by simpa using hr0
      have hr5 : (1 : ℂ) + ((ρ : ℂ) - 1) ≠ 0 := by simpa using hr0
      simp only [Zt, zeroTerm]
      rw [cpow_neg_one]
      field_simp
      ring
    have hS := ((h3.sub h1).sub (h3.mul_left (1 / (x : ℂ)))).sub hZs.hasSum
    rw [show (fun ρ : {ρ : ℂ // Λf ρ = 0} => m ρ * zeroTerm x ((ρ : ℂ) - 1)) = _ from
      funext hterm, hS.tsum_eq]
    have : b = D χ 0 := by linear_combination -hb0
    rw [this]
    field_simp
    ring

end LLS.ShiftAux
