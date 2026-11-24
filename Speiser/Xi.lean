import Mathlib
import Erdos985.Analytic.Hadamard
import Erdos985.Analytic.XiGrowth
import Erdos985.Analytic.Principal.Identity.Zeros
import Erdos985.Analytic.ExplicitFormula.StepA.GammaFactor

/-!
# `Re ξ'/ξ(z) ≤ 0` to the left of the critical line, under RH

`xiZeta s = s (s - 1) Λ(s)` is erdos-985's entire version of Riemann's `ξ` (up to `1/2`).
Its Hadamard factorisation (`hadamard_logDeriv`) gives
`ξ'/ξ(z) = b + Σ_ρ m_ρ (1/(z-ρ) + 1/ρ)`. At `z = 0` the sum vanishes, so `b = ξ'(0)`; the
functional equation `ξ(1-s) = ξ(s)` gives `ξ'(1) = -ξ'(0)`, so at `z = 1`
`-2b = Σ_ρ m_ρ (1/(1-ρ) + 1/ρ)`. Under RH every `ρ` has `1 - ρ = conj ρ`, so
`Re (1/(1-ρ)) = Re (1/ρ)`, and subtracting half of the second identity from the first leaves
`Re ξ'/ξ(z) = Σ_ρ m_ρ Re (1/(z-ρ)) = Σ_ρ m_ρ (Re z - 1/2) / |z-ρ|²`, which is `≤ 0` when
`Re z ≤ 1/2`.

Then, at a point `s` of the strip where `ζ'(s) = 0`, the local factorisation
`ξ = s (s-1) Γℝ(s) ζ(s)` gives `ξ'/ξ(s) = 1/s + 1/(s-1) + Γℝ'/Γℝ(s)`.
-/

open Complex Erdos985.Analytic Erdos985.Analytic.PrincipalAux

namespace Speiser

lemma xiZeta_one : xiZeta 1 = 1 := by simp [xiZeta]

lemma xiZeta_one_sub (s : ℂ) : xiZeta (1 - s) = xiZeta s := by
  simp only [xiZeta, completedRiemannZeta₀_one_sub]; ring

lemma deriv_xiZeta_one : deriv xiZeta 1 = -deriv xiZeta 0 := by
  have h1 : HasDerivAt (fun s : ℂ => 1 - s) (-1) 0 := by
    simpa using (hasDerivAt_id (0 : ℂ)).const_sub 1
  have h2 : HasDerivAt xiZeta (deriv xiZeta 1) ((fun s : ℂ => 1 - s) 0) := by
    simpa using (differentiable_xiZeta 1).hasDerivAt
  have h3 := h2.comp (0 : ℂ) h1
  have h4 : (xiZeta ∘ fun s : ℂ => 1 - s) = xiZeta := funext fun s => xiZeta_one_sub s
  rw [h4] at h3
  rw [h3.deriv]; ring

/-- A zero of `ξ` is a zero of `ζ` in the critical strip (as in li-criterion-rh). -/
lemma mem_strip_of_xiZeta_eq_zero {ρ : ℂ} (hρ : xiZeta ρ = 0) :
    0 < ρ.re ∧ ρ.re < 1 ∧ riemannZeta ρ = 0 := by
  obtain ⟨h0, h1⟩ := xiZeta_zero_re_mem hρ
  refine ⟨h0, h1, ?_⟩
  have hρ0 : ρ ≠ 0 := fun h => by rw [h] at h0; simp at h0
  have hρ1 : ρ ≠ 1 := fun h => by rw [h] at h1; simp at h1
  rw [xiZeta_eq hρ0 hρ1] at hρ
  have hΛ : completedRiemannZeta ρ = 0 := by
    rcases mul_eq_zero.mp hρ with h | h
    · rcases mul_eq_zero.mp h with h | h
      · exact absurd h hρ0
      · exact absurd (sub_eq_zero.mp h) hρ1
    · exact h
  rw [riemannZeta_def_of_ne_zero hρ0, hΛ, zero_div]

/-- Under RH every zero of `ξ` lies on the critical line. -/
lemma re_eq_half_of_xiZeta_eq_zero (hRH : RiemannHypothesis) {ρ : ℂ} (hρ : xiZeta ρ = 0) :
    ρ.re = 1 / 2 := by
  obtain ⟨h0, h1, hζ⟩ := mem_strip_of_xiZeta_eq_zero hρ
  refine hRH ρ hζ ?_ ?_
  · rintro ⟨n, rfl⟩
    have : (-2 * ((n : ℂ) + 1)).re = -2 * ((n : ℝ) + 1) := by simp
    rw [this] at h0
    have : (0 : ℝ) ≤ n := n.cast_nonneg
    linarith
  · rintro rfl; simp at h1

lemma re_one_div_one_sub {ρ : ℂ} (hρ : ρ.re = 1 / 2) :
    ((1 : ℂ) / (1 - ρ)).re = ((1 : ℂ) / ρ).re := by
  simp only [one_div, inv_re, normSq_apply, sub_re, one_re, sub_im, one_im, hρ]
  ring

lemma re_one_div_sub_nonpos {z ρ : ℂ} (hρ : ρ.re = 1 / 2) (hz : z.re ≤ 1 / 2) :
    ((1 : ℂ) / (z - ρ)).re ≤ 0 := by
  simp only [one_div, inv_re, sub_re, hρ]
  exact div_nonpos_of_nonpos_of_nonneg (by linarith) (normSq_nonneg _)

/-- **Under RH, `Re ξ'/ξ(z) ≤ 0` for `Re z ≤ 1/2`.** -/
theorem re_logDeriv_xiZeta_nonpos (hRH : RiemannHypothesis) {z : ℂ} (hz : xiZeta z ≠ 0)
    (hre : z.re ≤ 1 / 2) : (deriv xiZeta z / xiZeta z).re ≤ 0 := by
  have hx0 : xiZeta 0 ≠ 0 := by rw [xiZeta_zero]; exact one_ne_zero
  obtain ⟨-, b, hb⟩ := hadamard_logDeriv differentiable_xiZeta hx0 xiZeta_growth
  obtain ⟨-, h0⟩ := hb 0 hx0
  obtain ⟨hs1, h1⟩ := hb 1 (by rw [xiZeta_one]; exact one_ne_zero)
  obtain ⟨hsz, hz'⟩ := hb z hz
  have hb0 : deriv xiZeta 0 = b := by
    rw [xiZeta_zero, div_one] at h0
    rw [h0]; simp
  rw [xiZeta_one, div_one, deriv_xiZeta_one, hb0] at h1
  set m : {ρ : ℂ // xiZeta ρ = 0} → ℂ := fun ρ => (analyticOrderNatAt xiZeta ρ : ℂ)
  have H := (hsz.hasSum.sub (hs1.hasSum.mul_left (1 / 2)))
  have key : deriv xiZeta z / xiZeta z =
      (∑' ρ : {ρ : ℂ // xiZeta ρ = 0}, m ρ * (1 / (z - ρ) + 1 / ρ)) -
        1 / 2 * ∑' ρ : {ρ : ℂ // xiZeta ρ = 0}, m ρ * (1 / (1 - ρ) + 1 / ρ) := by
    rw [hz']; linear_combination (-(1 : ℂ) / 2) * h1
  rw [key]
  refine (Complex.hasSum_re H).nonpos fun ρ => ?_
  have hρ := re_eq_half_of_xiZeta_eq_zero hRH ρ.2
  have h12 : ((1 : ℂ) / 2).re = 1 / 2 := by norm_num
  have h12' : ((1 : ℂ) / 2).im = 0 := by norm_num
  have hm' : (0 : ℝ) ≤ (analyticOrderNatAt xiZeta (ρ : ℂ) : ℝ) := Nat.cast_nonneg _
  have := re_one_div_sub_nonpos hρ hre
  simp only [sub_re, mul_re, add_re, natCast_re, natCast_im, zero_mul, sub_zero,
    re_one_div_one_sub hρ, h12, h12']
  nlinarith [mul_nonpos_of_nonneg_of_nonpos hm' this]

/-- At a critical point `s` of `ζ` with `Re s > 0`, `s ≠ 1`, `ζ(s) ≠ 0`:
`ξ'/ξ(s) = 1/s + 1/(s-1) - (1/2) log π + (1/2) ψ(s/2)`. -/
theorem logDeriv_xiZeta_of_deriv_eq_zero {s : ℂ} (hs0 : 0 < s.re) (hs1 : s ≠ 1)
    (hζ : riemannZeta s ≠ 0) (hd : deriv riemannZeta s = 0) :
    deriv xiZeta s / xiZeta s =
      1 / s + 1 / (s - 1) + (-(1 / 2) * (Real.log Real.pi : ℂ) + (1 / 2) * digamma (s / 2)) := by
  set L := -(1 / 2) * (Real.log Real.pi : ℂ) + (1 / 2) * digamma (s / 2)
  set f : ℂ → ℂ := fun w => w * (w - 1) * Gammaℝ w with hf
  have hsne0 : s ≠ 0 := fun h => by rw [h] at hs0; simp at hs0
  have hsm1 : s - 1 ≠ 0 := sub_ne_zero.mpr hs1
  have hΓ : Gammaℝ s ≠ 0 := Gammaℝ_ne_zero_of_re_pos hs0
  have hfd : HasDerivAt f ((2 * s - 1) * Gammaℝ s + s * (s - 1) * (Gammaℝ s * L)) s := by
    have h1 : HasDerivAt (fun w : ℂ => w * (w - 1)) (2 * s - 1) s := by
      have := (hasDerivAt_id' s).mul ((hasDerivAt_id' s).sub_const 1)
      convert this using 1; ring
    exact h1.mul (StepAAux.hasDerivAt_Gammaℝ hs0)
  have hζd : HasDerivAt riemannZeta 0 s := by
    rw [← hd]; exact (differentiableAt_riemannZeta hs1).hasDerivAt
  have hprod := hfd.mul hζd
  have hev : xiZeta =ᶠ[nhds s] fun w => f w * riemannZeta w := by
    have hU : IsOpen ({w : ℂ | 0 < w.re} ∩ {1}ᶜ) :=
      (isOpen_lt continuous_const continuous_re).inter isOpen_compl_singleton
    filter_upwards [hU.mem_nhds ⟨hs0, hs1⟩] with w hw
    have hw0 : w ≠ 0 := fun h => by have := hw.1; rw [h] at this; simp at this
    have hw1 : w ≠ 1 := hw.2
    rw [xiZeta_eq hw0 hw1, riemannZeta_def_of_ne_zero hw0, hf]
    simp only
    rw [mul_assoc (w * (w - 1)), mul_div_cancel₀ _ (Gammaℝ_ne_zero_of_re_pos hw.1)]
  have hξd := hprod.congr_of_eventuallyEq hev
  rw [hξd.deriv, hev.eq_of_nhds, hf]
  simp only [mul_zero, add_zero]
  field_simp
  ring

end Speiser
