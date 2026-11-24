import Erdos985.Analytic.Principal

/-!
# A weighted zero sum for `ξ` under RH

If `0 ≤ w(ρ) ≤ min(A, B/‖ρ(ρ+1)‖)` for every zero `ρ` of `ξ`, with `B ≤ A σ²` and `σ > 3/2`, then
`Σ_ρ m_ρ w(ρ) ≤ 2Aσ (L(1/2 + σ) + 1/40)`, where
`L(s) = 1/s + 1/(s−1) + ½ log(s/2) − ½ log π` bounds `Re ξ'/ξ(s)` for real `s > 2`.

Pointwise (RH, `ρ = 1/2 + iγ`): `min(A, B/(¼+γ²)) ≤ 2Aσ²/(σ²+γ²) = 2Aσ · Re 1/(s−ρ)` with
`s = 1/2 + σ`, and `Re 1/ρ > 0`. Hadamard's product gives
`Σ m Re(1/(s−ρ) + 1/ρ) = Re ξ'/ξ(s) − Re ξ'/ξ(0)` and `−Re ξ'/ξ(0) = Re Λ₀(1) < 1/40`.
-/

namespace Cramer

open Complex Erdos985.Analytic ArithmeticFunction

section RH

open Erdos985.Analytic.PrincipalAux

/-- Under RH, `ξ` has no zeros with `Re s > 1/2`. (Same proof as robin-rh's `Robin/RH/Bach.lean`.) -/
theorem xiZeta_ne_zero_of_half_lt_RH (hRH : RiemannHypothesis) {s : ℂ}
    (hs : 1 / 2 < s.re) : xiZeta s ≠ 0 := by
  intro h
  have hs0 : s ≠ 0 := by rintro rfl; norm_num at hs
  have hs1 : s ≠ 1 := by rintro rfl; rw [xiZeta_one] at h; norm_num at h
  rw [xiZeta_eq hs0 hs1] at h
  have hs1' : s - 1 ≠ 0 := sub_ne_zero.mpr hs1
  have hΛ : completedRiemannZeta s = 0 := by
    rcases mul_eq_zero.mp h with h | h
    · rcases mul_eq_zero.mp h with h | h
      · exact absurd h hs0
      · exact absurd h hs1'
    · exact h
  have hζ : riemannZeta s = 0 := by rw [riemannZeta_def_of_ne_zero hs0, hΛ, zero_div]
  have htriv : ¬∃ n : ℕ, s = -2 * (n + 1) := by
    rintro ⟨n, rfl⟩
    have : (-2 * ((n : ℂ) + 1)).re = -2 * ((n : ℝ) + 1) := by simp
    rw [this] at hs
    have : (0 : ℝ) ≤ n := n.cast_nonneg
    linarith
  have := hRH s hζ htriv hs1
  linarith

theorem xiZeta_zero_re_RH (hRH : RiemannHypothesis) {ρ : ℂ} (hρ : xiZeta ρ = 0) :
    ρ.re = 1 / 2 := by
  have h1 : ¬ 1 / 2 < ρ.re := fun h => xiZeta_ne_zero_of_half_lt_RH hRH h hρ
  have h2 : ¬ 1 / 2 < (1 - ρ).re := fun h =>
    xiZeta_ne_zero_of_half_lt_RH hRH h (by rw [xiZeta_one_sub]; exact hρ)
  simp only [sub_re, one_re] at h2
  linarith

end RH

/-- The upper bound for `Re ξ'/ξ(s)` at real `s > 2`. -/
noncomputable def Lup (s : ℝ) : ℝ :=
  1 / s + 1 / (s - 1) + (1 / 2) * Real.log (s / 2) - (1 / 2) * Real.log Real.pi

lemma LSeries_vonMangoldt_real {s : ℝ} (hs : 1 < s) :
    LSeries (fun n => ((Λ n : ℝ) : ℂ)) (s : ℂ) = ((∑' n : ℕ, (Λ n : ℝ) / (n : ℝ) ^ s : ℝ) : ℂ) := by
  rw [LSeries, Complex.ofReal_tsum]
  refine tsum_congr fun n => ?_
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  · rw [LSeries.term_of_ne_zero hn]
    push_cast
    congr 1
    rw [show ((n : ℂ)) = ((n : ℝ) : ℂ) by push_cast; rfl, ← Complex.ofReal_cpow n.cast_nonneg]

/-- `Re ζ'/ζ(s) ≤ 0` for real `s > 1`. -/
lemma re_logDeriv_zeta_nonpos {s : ℝ} (hs : 1 < s) :
    (deriv riemannZeta (s : ℂ) / riemannZeta (s : ℂ)).re ≤ 0 := by
  have key := LSeries_vonMangoldt_eq_deriv_riemannZeta_div (s := (s : ℂ)) (by simpa using hs)
  have e : deriv riemannZeta (s : ℂ) / riemannZeta (s : ℂ)
      = -((∑' n : ℕ, (Λ n : ℝ) / (n : ℝ) ^ s : ℝ) : ℂ) := by
    rw [← LSeries_vonMangoldt_real hs, key]; ring
  rw [e, neg_re, ofReal_re, neg_nonpos]
  exact tsum_nonneg fun n => div_nonneg vonMangoldt_nonneg (by positivity)

/-- `Re ξ'/ξ(s) ≤ L(s)` for real `s > 2`. -/
lemma re_logDeriv_xi_le {s : ℝ} (hs : 2 < s) :
    (deriv xiZeta (s : ℂ) / xiZeta (s : ℂ)).re ≤ Lup s := by
  have hs' : 1 < (s : ℂ).re := by simp; linarith
  have h := PrincipalAux.logDeriv_riemannZeta_eq hs'
  have hξ : deriv xiZeta (s : ℂ) / xiZeta (s : ℂ) = deriv riemannZeta (s : ℂ) / riemannZeta (s : ℂ)
      + 1 / (s : ℂ) + 1 / ((s : ℂ) - 1) + gammaLogDeriv (1 : DirichletCharacter ℂ 1) (s : ℂ) := by
    rw [h]; ring
  have hz := re_logDeriv_zeta_nonpos (s := s) (by linarith)
  have hdig : (digamma ((s : ℂ) / 2)).re ≤ Real.log (s / 2) := by
    have e : (s : ℂ) / 2 = ((s / 2 : ℝ) : ℂ) := by push_cast; ring
    rw [e, BoundsAux.digamma_ofReal (by linarith), ofReal_re]
    exact (BoundsAux.rD_bounds (by linarith)).2
  rw [hξ, PrincipalAux.gammaLogDeriv_one]
  have e1 : (1 / (s : ℂ)).re = 1 / s := by
    rw [show (1 / (s : ℂ)) = ((1 / s : ℝ) : ℂ) by push_cast; ring, ofReal_re]
  have e2 : (1 / ((s : ℂ) - 1)).re = 1 / (s - 1) := by
    rw [show (1 / ((s : ℂ) - 1)) = ((1 / (s - 1) : ℝ) : ℂ) by push_cast; ring, ofReal_re]
  simp only [add_re, e1, e2, mul_re, neg_re, ofReal_re, ofReal_im, mul_zero, sub_zero]
  simp only [one_div, inv_re, normSq_ofNat, div_ofNat_re, one_re, inv_im, one_im, div_ofNat_im,
    neg_zero, zero_div, zero_mul, sub_zero, re_ofNat, im_ofNat] at *
  unfold Lup
  norm_num
  nlinarith

/-- The Hadamard constant: `−Re ξ'/ξ(0) = Re Λ₀(1) < 1/40`. -/
lemma neg_re_logDeriv_xi_zero_lt : -(deriv xiZeta 0 / xiZeta 0).re < 1 / 40 := by
  rw [PrincipalAux.deriv_xiZeta_zero, xiZeta_zero, div_one, neg_re, neg_neg]
  have h01 : completedRiemannZeta₀ 0 = completedRiemannZeta₀ 1 := by
    rw [← completedRiemannZeta₀_one_sub]; norm_num
  have h := PrincipalAux.re_two_completedRiemannZeta₀_one
  have h2 := PrincipalAux.two_add_gamma_sub_log_lt
  rw [h01]
  simp only [mul_re, re_ofNat, im_ofNat, zero_mul, sub_zero] at h
  linarith

/-- `Σ m Re(1/(s−ρ) + 1/ρ) ≤ L(s) + 1/40` for real `s > 2` (no RH needed). -/
theorem zeroSum_re_le {s : ℝ} (hs : 2 < s) :
    Summable (fun ρ : {ρ : ℂ // xiZeta ρ = 0} =>
      ((analyticOrderNatAt xiZeta ρ : ℂ) * (1 / ((s : ℂ) - ρ) + 1 / ρ)).re) ∧
    ∑' ρ : {ρ : ℂ // xiZeta ρ = 0},
      ((analyticOrderNatAt xiZeta ρ : ℂ) * (1 / ((s : ℂ) - ρ) + 1 / ρ)).re ≤ Lup s + 1 / 40 := by
  have hx0 : xiZeta 0 ≠ 0 := by rw [xiZeta_zero]; norm_num
  have hxs : xiZeta (s : ℂ) ≠ 0 := fun h => by
    have := (xiZeta_zero_re_mem h).2; simp at this; linarith
  obtain ⟨-, b, H⟩ := hadamard_logDeriv differentiable_xiZeta hx0 xiZeta_growth
  obtain ⟨-, e0⟩ := H 0 hx0
  obtain ⟨hsum, es⟩ := H (s : ℂ) hxs
  have hz : ∀ ρ : {ρ : ℂ // xiZeta ρ = 0},
      (analyticOrderNatAt xiZeta ρ : ℂ) * (1 / (0 - (ρ : ℂ)) + 1 / ρ) = 0 := by
    intro ρ; simp
  simp only [hz, tsum_zero, add_zero] at e0
  have hre := Complex.reCLM.hasSum hsum.hasSum
  simp only [Complex.reCLM_apply] at hre
  refine ⟨hre.summable, ?_⟩
  rw [hre.tsum_eq]
  have e : (∑' ρ : {ρ : ℂ // xiZeta ρ = 0},
      (analyticOrderNatAt xiZeta ρ : ℂ) * (1 / ((s : ℂ) - ρ) + 1 / ρ))
      = deriv xiZeta (s : ℂ) / xiZeta (s : ℂ) - deriv xiZeta 0 / xiZeta 0 := by
    rw [es, e0]; ring
  rw [e, sub_re]
  linarith [re_logDeriv_xi_le hs, neg_re_logDeriv_xi_zero_lt]

/-- Pointwise comparison on the critical line. -/
lemma weight_le {ρ : ℂ} (hρ : ρ.re = 1 / 2) {σ A B w : ℝ} (hσ : 0 < σ) (hA : 0 ≤ A)
    (hB0 : 0 ≤ B) (hB : B ≤ A * σ ^ 2) (hwA : w ≤ A) (hwB : w ≤ B / ‖ρ * (ρ + 1)‖) :
    w ≤ 2 * A * σ * (1 / (((1 / 2 + σ : ℝ) : ℂ) - ρ) + 1 / ρ).re := by
  have hq := PrincipalAux.inv_norm_mul_le_re hρ
  obtain ⟨x, γ⟩ := ρ
  simp only at hρ
  subst hρ
  have hre1 : (1 / (1 - (⟨1 / 2, γ⟩ : ℂ)) + 1 / ⟨1 / 2, γ⟩).re = 1 / (1 / 4 + γ ^ 2) := by
    simp [normSq_apply]
    field_simp
    ring
  rw [hre1] at hq
  have hre2 : (1 / (((1 / 2 + σ : ℝ) : ℂ) - ⟨1 / 2, γ⟩) + 1 / ⟨1 / 2, γ⟩).re
      = σ / (σ ^ 2 + γ ^ 2) + (1 / 2) / (1 / 4 + γ ^ 2) := by
    simp [normSq_apply]
    field_simp
    ring
  rw [hre2]
  have hp1 : 0 < 1 / 4 + γ ^ 2 := by positivity
  have hp2 : 0 < σ ^ 2 + γ ^ 2 := by positivity
  have hwB' : w ≤ B / (1 / 4 + γ ^ 2) := by
    refine hwB.trans ?_
    rw [div_eq_mul_one_div B, div_eq_mul_one_div B]
    exact mul_le_mul_of_nonneg_left hq hB0
  have hextra : 0 ≤ 2 * A * σ * ((1 / 2) / (1 / 4 + γ ^ 2)) := by positivity
  have hmain : w ≤ 2 * A * σ * (σ / (σ ^ 2 + γ ^ 2)) := by
    rw [show 2 * A * σ * (σ / (σ ^ 2 + γ ^ 2)) = 2 * A * σ ^ 2 / (σ ^ 2 + γ ^ 2) by ring]
    rcases le_total (γ ^ 2) (σ ^ 2) with hg | hg
    · rw [le_div_iff₀ hp2]
      nlinarith
    · have : B / (1 / 4 + γ ^ 2) ≤ 2 * A * σ ^ 2 / (σ ^ 2 + γ ^ 2) := by
        rw [div_le_div_iff₀ hp1 hp2]
        nlinarith [sq_nonneg γ, sq_nonneg σ]
      linarith
  nlinarith

/-- **The weighted zero sum under RH.** -/
theorem weighted_zeroSum_le (hRH : RiemannHypothesis) {σ A B : ℝ} (hσ : 3 / 2 < σ) (hA : 0 ≤ A)
    (hB0 : 0 ≤ B) (hB : B ≤ A * σ ^ 2) (w : {ρ : ℂ // xiZeta ρ = 0} → ℝ) (hw0 : ∀ ρ, 0 ≤ w ρ)
    (hwA : ∀ ρ, w ρ ≤ A) (hwB : ∀ ρ : {ρ : ℂ // xiZeta ρ = 0}, w ρ ≤ B / ‖(ρ : ℂ) * ((ρ : ℂ) + 1)‖) :
    Summable (fun ρ : {ρ : ℂ // xiZeta ρ = 0} => (analyticOrderNatAt xiZeta ρ : ℝ) * w ρ) ∧
    ∑' ρ : {ρ : ℂ // xiZeta ρ = 0}, (analyticOrderNatAt xiZeta ρ : ℝ) * w ρ ≤ 2 * A * σ * (Lup (1 / 2 + σ) + 1 / 40) := by
  obtain ⟨hS, hle⟩ := zeroSum_re_le (s := 1 / 2 + σ) (by linarith)
  set r : {ρ : ℂ // xiZeta ρ = 0} → ℝ := fun ρ =>
    ((analyticOrderNatAt xiZeta ρ : ℂ) * (1 / (((1 / 2 + σ : ℝ) : ℂ) - ρ) + 1 / ρ)).re
  have hr : ∀ ρ : {ρ : ℂ // xiZeta ρ = 0}, r ρ = (analyticOrderNatAt xiZeta ρ : ℝ) *
      (1 / (((1 / 2 + σ : ℝ) : ℂ) - ρ) + 1 / ρ).re := by
    intro ρ; simp [r, mul_re]
  have hcmp : ∀ ρ : {ρ : ℂ // xiZeta ρ = 0}, (analyticOrderNatAt xiZeta ρ : ℝ) * w ρ ≤ 2 * A * σ * r ρ := by
    intro ρ
    rw [hr]
    have := weight_le (xiZeta_zero_re_RH hRH ρ.2) (by linarith) hA hB0 hB (hwA ρ) (hwB ρ)
    have hm : (0 : ℝ) ≤ analyticOrderNatAt xiZeta ρ := Nat.cast_nonneg _
    nlinarith
  have hnn : ∀ ρ : {ρ : ℂ // xiZeta ρ = 0}, 0 ≤ (analyticOrderNatAt xiZeta ρ : ℝ) * w ρ :=
    fun ρ => mul_nonneg (Nat.cast_nonneg _) (hw0 ρ)
  have hS' : Summable fun ρ : {ρ : ℂ // xiZeta ρ = 0} => 2 * A * σ * r ρ := hS.mul_left _
  have hsum := Summable.of_nonneg_of_le hnn hcmp hS'
  refine ⟨hsum, ?_⟩
  calc _ ≤ ∑' ρ : {ρ : ℂ // xiZeta ρ = 0}, 2 * A * σ * r ρ := hsum.tsum_le_tsum hcmp hS'
    _ = 2 * A * σ * ∑' ρ : {ρ : ℂ // xiZeta ρ = 0}, r ρ := tsum_mul_left
    _ ≤ 2 * A * σ * (Lup (1 / 2 + σ) + 1 / 40) := by
        apply mul_le_mul_of_nonneg_left hle; positivity

end Cramer
