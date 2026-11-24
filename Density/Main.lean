import Density.ZeroCount

/-!
# The density hypothesis from RH

Under `RiemannHypothesis` (Mathlib's statement), `ζ` has no zeros with `Re s > 1/2` and
`Im s > 0`, so `N(σ, T) = 0` for `σ > 1/2`. At `σ = 1/2` the exponent is `1 + ε`, and the
Riemann–von Mangoldt bound `N(1/2, T) ≤ C T log T ≤ (C / ε) T^{1+ε}`
(`Density.zeroCountOn_riemannZeta_le_of_subset_strip`) closes it. The constant `C / ε` depends
only on `ε`, as the statement requires.
-/

open Complex

namespace DensityHypothesis

/-- Under RH, `ζ` does not vanish at `s` with `Re s > 1/2` and `Im s ≠ 0`. -/
theorem riemannZeta_ne_zero_of_RH (hRH : RiemannHypothesis) {s : ℂ} (hs : 1 / 2 < s.re)
    (him : s.im ≠ 0) : riemannZeta s ≠ 0 := by
  intro h0
  have htriv : ¬∃ n : ℕ, s = -2 * (n + 1) := by
    rintro ⟨n, rfl⟩
    apply him
    simp
  have h1 : s ≠ 1 := by rintro rfl; simp at him
  have := hRH s h0 htriv h1
  linarith

/-- Under RH, `N(σ, T) = 0` for every `σ > 1/2`. -/
theorem zetaZeroCount_eq_zero_of_RH (hRH : RiemannHypothesis) {σ : ℝ} (hσ : 1 / 2 < σ)
    (T : ℝ) : zetaZeroCount σ T = 0 :=
  Complex.zeroCountOn_eq_zero_of_forall_ne_zero fun _ hs =>
    riemannZeta_ne_zero_of_RH hRH (hσ.trans_le hs.1) hs.2.2.1.ne'

/-- **The density hypothesis from RH.** -/
theorem densityHypothesis_of_RH (hRH : RiemannHypothesis) : Statement := by
  intro ε hε
  obtain ⟨C, hC, hcount⟩ := Density.zeroCountOn_riemannZeta_le_of_subset_strip
  refine ⟨C / ε, div_pos hC hε, fun σ T hσ hσ1 hT => ?_⟩
  have hT0 : 0 < T := by linarith
  have hpos : 0 ≤ C / ε * T ^ (2 * (1 - σ) + ε) := by positivity
  rcases hσ.lt_or_eq with hlt | heq
  · rw [zetaZeroCount_eq_zero_of_RH hRH hlt T, Nat.cast_zero]
    exact hpos
  · subst heq
    have hS : {s : ℂ | 1 / 2 ≤ s.re ∧ s.re ≤ 1 ∧ 0 < s.im ∧ s.im ≤ T} ⊆
        {s : ℂ | 0 ≤ s.re ∧ s.re ≤ 1 ∧ |s.im| ≤ T} := fun s hs =>
      ⟨by linarith [hs.1], hs.2.1, by rw [abs_of_pos hs.2.2.1]; exact hs.2.2.2⟩
    refine (hcount T hT _ hS).trans ?_
    have hlog : Real.log T ≤ T ^ ε / ε := Real.log_le_rpow_div hT0.le hε
    have hexp : T ^ (2 * (1 - 1 / 2) + ε) = T * T ^ ε := by
      rw [show 2 * (1 - 1 / 2 : ℝ) + ε = 1 + ε by ring, Real.rpow_add hT0, Real.rpow_one]
    rw [hexp]
    calc C * T * Real.log T ≤ C * T * (T ^ ε / ε) := by gcongr
      _ = C / ε * (T * T ^ ε) := by ring

/-- The density hypothesis implies the Guth–Maynard bound: for `T ≥ 2` and `σ ≤ 1`,
`T^{2(1-σ)+ε} ≤ T^{(30/13)(1-σ)+ε}`. -/
theorem guthMaynard_of_statement (h : Statement) : GuthMaynardStatement := by
  intro ε hε
  obtain ⟨C, hC, hb⟩ := h ε hε
  refine ⟨C, hC, fun σ T hσ hσ1 hT => (hb σ T hσ hσ1 hT).trans ?_⟩
  gcongr
  · linarith
  · linarith

/-- **The Guth–Maynard zero-density statement from RH** (as a corollary of the density
hypothesis, not via Guth–Maynard's unconditional argument). -/
theorem guthMaynard_of_RH (hRH : RiemannHypothesis) : GuthMaynardStatement :=
  guthMaynard_of_statement (densityHypothesis_of_RH hRH)

end DensityHypothesis
