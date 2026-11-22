import Lindelof.RH

/-!
# Step 2: under RH, `|ξ(σ + it)|` increases in `σ ≥ 1/2`

See `docs/BLUEPRINT.md`, Step 2: the Hadamard product (`hadamard_logDeriv`) together with
`ξ(1 - s) = ξ(s)` and `ξ(s̄) = conj ξ(s)` gives `2 ∂σ log|ξ| = Σ_ρ m_ρ (2σ - 1)/|s - ρ|² ≥ 0`.
-/

namespace Lindelof

open Complex Erdos985.Analytic Erdos985.Analytic.PrincipalAux ComplexConjugate

/-- `ξ(s̄) = conj ξ(s)`. -/
theorem xiZeta_conj (s : ℂ) : xiZeta (conj s) = conj (xiZeta s) := by
  by_cases h0 : s = 0
  · subst h0; simp [xiZeta_zero]
  by_cases h1 : s = 1
  · subst h1; simp [xiZeta_one]
  have h0' : conj s ≠ 0 := by simpa using h0
  have h1' : conj s ≠ 1 := by
    intro h; apply h1; simpa using congrArg conj h
  rw [xiZeta_eq h0' h1', xiZeta_eq h0 h1, completedRiemannZeta_conj]
  simp

/-- `ξ'(s̄) = conj ξ'(s)`. -/
theorem deriv_xiZeta_conj (s : ℂ) : deriv xiZeta (conj s) = conj (deriv xiZeta s) := by
  have hfun : (conj ∘ xiZeta ∘ conj) = xiZeta := by
    funext z; simp [Function.comp, xiZeta_conj]
  have h := congrFun (deriv_conj_conj (f := xiZeta)) (conj s)
  rw [hfun] at h
  simp only [Function.comp, conj_conj] at h
  rw [h]

/-- `ξ'(1 - s) = -ξ'(s)`. -/
theorem deriv_xiZeta_one_sub (s : ℂ) : deriv xiZeta (1 - s) = -deriv xiZeta s := by
  have h : HasDerivAt (fun z => xiZeta (1 - z)) (deriv xiZeta (1 - s) * (-1)) s :=
    (differentiable_xiZeta (1 - s)).hasDerivAt.comp s ((hasDerivAt_id s).const_sub 1)
  have hfun : (fun z => xiZeta (1 - z)) = xiZeta := funext xiZeta_one_sub
  rw [hfun] at h
  rw [(differentiable_xiZeta s).hasDerivAt.unique h]
  ring

/-- Under RH, `Re ξ'/ξ(z) ≥ 0` for `Re z > 1/2`: subtracting the Hadamard expansions at `z` and
`1 - z̄` gives `2 Re ξ'/ξ(z) = Σ_ρ m_ρ (2 Re z - 1)/|z - ρ|²`. -/
theorem re_logDeriv_xiZeta_nonneg (hRH : RiemannHypothesis) {z : ℂ} (hz : 1 / 2 < z.re) :
    0 ≤ (deriv xiZeta z / xiZeta z).re := by
  obtain ⟨-, b, hb⟩ := hadamard_logDeriv differentiable_xiZeta
    (by rw [xiZeta_zero]; exact one_ne_zero) xiZeta_growth
  set w := 1 - conj z with hw
  have hz0 := xiZeta_ne_zero_of_RH hRH hz
  have hw0 : xiZeta w ≠ 0 := by
    rw [hw, xiZeta_one_sub, xiZeta_conj]; simpa using hz0
  have hLw : deriv xiZeta w / xiZeta w = -conj (deriv xiZeta z / xiZeta z) := by
    rw [hw, deriv_xiZeta_one_sub, xiZeta_one_sub, deriv_xiZeta_conj, xiZeta_conj, map_div₀]
    ring
  obtain ⟨hsz, hz'⟩ := hb z hz0
  obtain ⟨hsw, hw'⟩ := hb w hw0
  set m : {ρ : ℂ // xiZeta ρ = 0} → ℂ := fun ρ => (analyticOrderNatAt xiZeta ρ : ℂ)
  have key : 2 * (deriv xiZeta z / xiZeta z).re = ∑' ρ : {ρ : ℂ // xiZeta ρ = 0},
      (m ρ * (1 / (z - ρ) + 1 / ρ) - m ρ * (1 / (w - ρ) + 1 / ρ)).re := by
    rw [← re_tsum (hsz.sub hsw), hsz.tsum_sub hsw]
    have e1 := hz'
    have e2 := hw'
    rw [hLw] at e2
    have : (∑' ρ : {ρ : ℂ // xiZeta ρ = 0}, m ρ * (1 / (z - ρ) + 1 / ρ)) -
        ∑' ρ : {ρ : ℂ // xiZeta ρ = 0}, m ρ * (1 / (w - ρ) + 1 / ρ) =
        deriv xiZeta z / xiZeta z + conj (deriv xiZeta z / xiZeta z) := by
      simp only [m]; rw [← sub_eq_iff_eq_add'.mpr e1, ← sub_eq_iff_eq_add'.mpr e2]; ring
    rw [this, add_re, conj_re]; ring
  have hnn : 0 ≤ ∑' ρ : {ρ : ℂ // xiZeta ρ = 0},
      (m ρ * (1 / (z - ρ) + 1 / ρ) - m ρ * (1 / (w - ρ) + 1 / ρ)).re := by
    refine tsum_nonneg fun ρ => ?_
    have hρ : (ρ : ℂ).re = 1 / 2 := xiZeta_zero_re_of_RH hRH ρ.2
    have hN : normSq (w - ρ) = normSq (z - ρ) := by
      simp only [hw, normSq_apply, sub_re, sub_im, one_re, one_im, conj_re, conj_im, hρ]
      ring
    have hterm : m ρ * (1 / (z - ρ) + 1 / ρ) - m ρ * (1 / (w - ρ) + 1 / ρ) =
        m ρ * ((z - ρ)⁻¹ - (w - ρ)⁻¹) := by ring
    rw [hterm]
    rw [mul_re, sub_re, sub_im, inv_re, inv_re, hN]
    simp only [m, natCast_re, natCast_im, zero_mul, sub_zero, sub_re, hρ, hw, one_re, conj_re]
    have : z.re - 1 / 2 - (1 - z.re - 1 / 2) = 2 * z.re - 1 := by ring
    rw [← sub_div, this]
    exact mul_nonneg (Nat.cast_nonneg _) (div_nonneg (by linarith) (normSq_nonneg _))
  linarith

/-- Under RH, `σ ↦ ‖ξ(σ + it)‖` is monotone on `[1/2, ∞)`. -/
theorem norm_xiZeta_le_of_half_le (hRH : RiemannHypothesis) (t : ℝ) {σ σ' : ℝ}
    (hσ : 1 / 2 ≤ σ) (hσσ' : σ ≤ σ') :
    ‖xiZeta (σ + t * I)‖ ≤ ‖xiZeta (σ' + t * I)‖ := by
  set F : ℝ → ℂ := fun x => xiZeta (x + t * I) with hFdef
  have hF : ∀ x : ℝ, HasDerivAt F (deriv xiZeta (x + t * I)) x := fun x =>
    HasDerivAt.comp_ofReal (e := fun z => xiZeta (z + t * I))
      (differentiable_xiZeta _).hasDerivAt.comp_add_const
  have hh : ∀ x : ℝ, HasDerivAt (fun x => ‖F x‖ ^ 2)
      (2 * inner ℝ (F x) (deriv xiZeta (x + t * I))) x := fun x => (hF x).norm_sq
  have hmono : MonotoneOn (fun x => ‖F x‖ ^ 2) (Set.Ici (1 / 2)) := by
    refine monotoneOn_of_deriv_nonneg (convex_Ici _)
      (fun x _ => (hh x).continuousAt.continuousWithinAt)
      (fun x _ => (hh x).differentiableAt.differentiableWithinAt) fun x hx => ?_
    rw [interior_Ici] at hx
    rw [(hh x).deriv, Complex.inner]
    have hre : 1 / 2 < ((x : ℂ) + t * I).re := by simpa using hx
    have hne := xiZeta_ne_zero_of_RH hRH hre
    have hL := re_logDeriv_xiZeta_nonneg hRH hre
    have : deriv xiZeta (x + t * I) * conj (F x) =
        (deriv xiZeta (x + t * I) / xiZeta (x + t * I)) * (normSq (F x) : ℂ) := by
      rw [← mul_conj]; simp only [hFdef]; field_simp
    rw [this, re_mul_ofReal]
    have := normSq_nonneg (F x)
    positivity
  have h2 := hmono (Set.mem_Ici.mpr hσ) (Set.mem_Ici.mpr (hσ.trans hσσ')) hσσ'
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp h2

end Lindelof
