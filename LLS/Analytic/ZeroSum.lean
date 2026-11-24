import LLS.Defs

/-! # The zero sum `Σ m_ρ/|ρ|²` under GRH (Hadamard at `s = 1` and `s = 0`) -/

namespace LLS

open Complex Erdos985 Erdos985.Analytic

variable {N : ℕ} [NeZero N]

/-- On the critical line, `Re (1/(1 − ρ) + 1/ρ) = 1/|ρ|²`. -/
lemma re_pair_one_eq {ρ : ℂ} (hρ : ρ.re = 1 / 2) (m : ℕ) :
    ((m : ℂ) * (1 / (1 - ρ) + 1 / ρ)).re = (m : ℝ) / ‖ρ‖ ^ 2 := by
  obtain ⟨a, γ⟩ := ρ
  simp only at hρ
  subst hρ
  rw [← Complex.normSq_eq_norm_sq]
  simp [normSq_apply]
  have h : (1 : ℝ) - 2⁻¹ = 2⁻¹ := by norm_num
  rw [h]
  have h1 : (0 : ℝ) < 2⁻¹ * 2⁻¹ + γ * γ := by nlinarith [mul_self_nonneg γ]
  field_simp
  ring

/-- Under GRH, `Σ_ρ m_ρ/|ρ|² = log N + Re D(1, χ) + Re D(1, χ⁻¹)` (LLS (2.4): `= 2|Re B(χ)|`). -/
theorem Z2_eq (hGRH : DirichletLNonvanishingRightOfHalf) {χ : DirichletCharacter ℂ N}
    (hprim : χ.IsPrimitive) (hχ : χ ≠ 1) :
    Summable (fun ρ : {ρ : ℂ // DirichletCharacter.completedLFunction χ ρ = 0} =>
        (analyticOrderNatAt (DirichletCharacter.completedLFunction χ) ρ : ℝ) / ‖(ρ : ℂ)‖ ^ 2) ∧
    Z2 χ = Real.log N + (D χ 1).re + (D χ⁻¹ 1).re := by
  have hχi : χ⁻¹ ≠ 1 := by simpa using hχ
  obtain ⟨-, b, H⟩ := hadamard_logDeriv (DirichletCharacter.differentiable_completedLFunction hχ)
    (completedLFunction_zero_ne_zero χ hχ hprim) (completedLFunction_growth χ hχ)
  set f := DirichletCharacter.completedLFunction χ with hf
  have h1 : f 1 ≠ 0 :=
    DirichletCharacter.completedLFunction_ne_zero_of_one_le_re χ (Or.inl hχ) (by simp)
  have hi1 : DirichletCharacter.completedLFunction χ⁻¹ 1 ≠ 0 :=
    DirichletCharacter.completedLFunction_ne_zero_of_one_le_re χ⁻¹ (Or.inl hχi) (by simp)
  have h0 : f 0 ≠ 0 := completedLFunction_zero_ne_zero χ hχ hprim
  obtain ⟨sA, eA⟩ := H 1 h1
  obtain ⟨-, eB⟩ := H 0 h0
  have hB0 : ∑' ρ : {ρ : ℂ // f ρ = 0}, (analyticOrderNatAt f ρ : ℂ) * (1 / (0 - ρ) + 1 / ρ)
      = 0 := by
    refine (tsum_congr fun ρ => ?_).trans tsum_zero
    rw [zero_sub, one_div_neg_eq_neg_one_div, neg_add_cancel, mul_zero]
  rw [hB0, add_zero] at eB
  have hFE := ZeroSumAux.logDeriv_functional_equation hprim hχ (s := 1) hi1
  rw [sub_self] at hFE
  have hval : ∑' ρ : {ρ : ℂ // f ρ = 0}, (analyticOrderNatAt f ρ : ℂ) * (1 / (1 - ρ) + 1 / ρ)
      = D χ 1 + (Real.log N + D χ⁻¹ 1) := by
    unfold D
    rw [← hFE, ← hf, eA, eB]; ring
  have hcrit : ∀ ρ : {ρ : ℂ // f ρ = 0}, (ρ : ℂ).re = 1 / 2 :=
    fun ρ => completedLFunction_zero_re hGRH hprim hχ ρ.2
  have hre := Complex.reCLM.hasSum sA.hasSum
  have hterm : (fun ρ : {ρ : ℂ // f ρ = 0} =>
      Complex.reCLM ((analyticOrderNatAt f ρ : ℂ) * (1 / (1 - (ρ : ℂ)) + 1 / ρ)))
      = fun ρ : {ρ : ℂ // f ρ = 0} => (analyticOrderNatAt f ρ : ℝ) / ‖(ρ : ℂ)‖ ^ 2 := by
    funext ρ
    exact re_pair_one_eq (hcrit ρ) _
  rw [hterm, hval] at hre
  refine ⟨hre.summable, ?_⟩
  unfold Z2
  rw [← hf, hre.tsum_eq]
  simp only [Complex.reCLM_apply, add_re, ofReal_re]
  ring

theorem Z2_nonneg (χ : DirichletCharacter ℂ N) : 0 ≤ Z2 χ :=
  tsum_nonneg fun _ => div_nonneg (Nat.cast_nonneg _) (by positivity)

end LLS
