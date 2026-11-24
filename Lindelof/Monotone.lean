import Lindelof.RH

/-!
# Step 2: under RH, `|ξ(σ + it)|` increases in `σ ≥ 1/2`

See `docs/BLUEPRINT.md`, Step 2: the Hadamard product (`hadamard_logDeriv`) together with
`ξ(1 - s) = ξ(s)` and `ξ(s̄) = conj ξ(s)` gives `2 ∂σ log|ξ| = Σ_ρ m_ρ (2σ - 1)/|s - ρ|² ≥ 0`.

The two halves are stated for any entire `f` of order one with zeros on the critical line
(`re_logDeriv_one_sub_conj_le`, `norm_le_of_re_logDeriv_ge`), so the Dirichlet case
(`Lindelof/DirichletCompleted.lean`) reuses them with `f = Λ(·, χ)`.
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

/-- **Generic Step 2 core.** If `f` is entire of order at most one, `f 0 ≠ 0`, and every zero of
`f` lies on `Re s = 1/2`, then `Re f'/f(1 - z̄) ≤ Re f'/f(z)` for `Re z > 1/2`: subtracting the
Hadamard expansions (`hadamard_logDeriv`) at `z` and `w = 1 - z̄` kills the constant, and each
zero contributes `m_ρ (2 Re z - 1)/|z - ρ|² ≥ 0`. -/
theorem re_logDeriv_one_sub_conj_le {f : ℂ → ℂ} (hf : Differentiable ℂ f) (hf0 : f 0 ≠ 0)
    (hgrowth : ∃ C : ℝ, ∀ z : ℂ, ‖f z‖ ≤ C * Real.exp (C * ‖z‖ * Real.log (‖z‖ + 2)))
    (hzeros : ∀ ρ : ℂ, f ρ = 0 → ρ.re = 1 / 2) {z : ℂ} (hz : 1 / 2 < z.re) :
    (deriv f (1 - conj z) / f (1 - conj z)).re ≤ (deriv f z / f z).re := by
  obtain ⟨-, b, hb⟩ := hadamard_logDeriv hf hf0 hgrowth
  set w := 1 - conj z with hw
  have hz0 : f z ≠ 0 := fun h => by have := hzeros z h; linarith
  have hw0 : f w ≠ 0 := fun h => by
    have := hzeros w h
    simp only [hw, sub_re, one_re, conj_re] at this
    linarith
  obtain ⟨hsz, hz'⟩ := hb z hz0
  obtain ⟨hsw, hw'⟩ := hb w hw0
  set m : {ρ : ℂ // f ρ = 0} → ℂ := fun ρ => (analyticOrderNatAt f ρ : ℂ)
  have key : (deriv f z / f z - deriv f w / f w).re = ∑' ρ : {ρ : ℂ // f ρ = 0},
      (m ρ * (1 / (z - ρ) + 1 / ρ) - m ρ * (1 / (w - ρ) + 1 / ρ)).re := by
    rw [← re_tsum (hsz.sub hsw), hsz.tsum_sub hsw, hz', hw']
    ring_nf
  have hnn : 0 ≤ ∑' ρ : {ρ : ℂ // f ρ = 0},
      (m ρ * (1 / (z - ρ) + 1 / ρ) - m ρ * (1 / (w - ρ) + 1 / ρ)).re := by
    refine tsum_nonneg fun ρ => ?_
    have hρ : (ρ : ℂ).re = 1 / 2 := hzeros ρ ρ.2
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
  rw [sub_re] at key
  linarith

/-- **Generic Step 2.** If `f` is entire, has no zeros on `Re s > 1/2`, and
`2 Re f'/f ≥ -c` there, then `σ ↦ e^{cσ} ‖f(σ + it)‖²` is monotone on `[1/2, ∞)`, i.e.
`‖f(σ + it)‖ ≤ e^{c(σ' - σ)/2} ‖f(σ' + it)‖` for `1/2 ≤ σ ≤ σ'`. -/
theorem norm_le_of_re_logDeriv_ge {f : ℂ → ℂ} (hf : Differentiable ℂ f) (c : ℝ)
    (hne : ∀ z : ℂ, 1 / 2 < z.re → f z ≠ 0)
    (hL : ∀ z : ℂ, 1 / 2 < z.re → -c ≤ 2 * (deriv f z / f z).re) (t : ℝ) {σ σ' : ℝ}
    (hσ : 1 / 2 ≤ σ) (hσσ' : σ ≤ σ') :
    ‖f (σ + t * I)‖ ≤ Real.exp (c * (σ' - σ) / 2) * ‖f (σ' + t * I)‖ := by
  set F : ℝ → ℂ := fun x => f (x + t * I) with hFdef
  have hF : ∀ x : ℝ, HasDerivAt F (deriv f (x + t * I)) x := fun x =>
    HasDerivAt.comp_ofReal (e := fun z => f (z + t * I))
      (hf _).hasDerivAt.comp_add_const
  have hh : ∀ x : ℝ, HasDerivAt (fun x => Real.exp (c * x) * ‖F x‖ ^ 2)
      (c * Real.exp (c * x) * ‖F x‖ ^ 2 +
        Real.exp (c * x) * (2 * inner ℝ (F x) (deriv f (x + t * I)))) x := by
    intro x
    have h1 : HasDerivAt (fun x => Real.exp (c * x)) (Real.exp (c * x) * c) x := by
      simpa using ((hasDerivAt_id x).const_mul c).exp
    convert h1.mul (hF x).norm_sq using 1
    ring
  have hmono : MonotoneOn (fun x => Real.exp (c * x) * ‖F x‖ ^ 2) (Set.Ici (1 / 2)) := by
    refine monotoneOn_of_deriv_nonneg (convex_Ici _)
      (fun x _ => (hh x).continuousAt.continuousWithinAt)
      (fun x _ => (hh x).differentiableAt.differentiableWithinAt) fun x hx => ?_
    rw [interior_Ici] at hx
    rw [(hh x).deriv, Complex.inner]
    have hre : 1 / 2 < ((x : ℂ) + t * I).re := by simpa using hx
    have hne' := hne _ hre
    have hL' := hL _ hre
    have : deriv f (x + t * I) * conj (F x) =
        (deriv f (x + t * I) / f (x + t * I)) * (normSq (F x) : ℂ) := by
      rw [← mul_conj]; simp only [hFdef]; field_simp
    rw [this, re_mul_ofReal, ← Complex.sq_norm]
    have he := Real.exp_pos (c * x)
    have hsq := sq_nonneg ‖F x‖
    have : c * Real.exp (c * x) * ‖F x‖ ^ 2 +
        Real.exp (c * x) * (2 * ((deriv f (↑x + ↑t * I) / f (↑x + ↑t * I)).re * ‖F x‖ ^ 2)) =
        Real.exp (c * x) * ‖F x‖ ^ 2 * (c + 2 * (deriv f (↑x + ↑t * I) / f (↑x + ↑t * I)).re) := by
      ring
    rw [this]
    exact mul_nonneg (by positivity) (by linarith)
  have h2 := hmono (Set.mem_Ici.mpr hσ) (Set.mem_Ici.mpr (hσ.trans hσσ')) hσσ'
  simp only at h2
  have hsplit : Real.exp (c * σ') = Real.exp (c * σ) * Real.exp (c * (σ' - σ) / 2) ^ 2 := by
    rw [← Real.exp_nat_mul, ← Real.exp_add]; congr 1; push_cast; ring
  rw [hsplit, mul_assoc] at h2
  have h3 := le_of_mul_le_mul_left h2 (Real.exp_pos _)
  rw [← mul_pow] at h3
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp h3

/-- Under RH, `Re ξ'/ξ(z) ≥ 0` for `Re z > 1/2`: by `re_logDeriv_one_sub_conj_le` and
`ξ'/ξ(1 - z̄) = -conj (ξ'/ξ(z))`. -/
theorem re_logDeriv_xiZeta_nonneg (hRH : RiemannHypothesis) {z : ℂ} (hz : 1 / 2 < z.re) :
    0 ≤ (deriv xiZeta z / xiZeta z).re := by
  have h := re_logDeriv_one_sub_conj_le differentiable_xiZeta
    (by rw [xiZeta_zero]; exact one_ne_zero) xiZeta_growth
    (fun ρ hρ => xiZeta_zero_re_of_RH hRH hρ) hz
  have hLw : deriv xiZeta (1 - conj z) / xiZeta (1 - conj z) =
      -conj (deriv xiZeta z / xiZeta z) := by
    rw [deriv_xiZeta_one_sub, xiZeta_one_sub, deriv_xiZeta_conj, xiZeta_conj, map_div₀]
    ring
  rw [hLw, neg_re, conj_re] at h
  linarith

/-- Under RH, `σ ↦ ‖ξ(σ + it)‖` is monotone on `[1/2, ∞)`. -/
theorem norm_xiZeta_le_of_half_le (hRH : RiemannHypothesis) (t : ℝ) {σ σ' : ℝ}
    (hσ : 1 / 2 ≤ σ) (hσσ' : σ ≤ σ') :
    ‖xiZeta (σ + t * I)‖ ≤ ‖xiZeta (σ' + t * I)‖ := by
  have h := norm_le_of_re_logDeriv_ge differentiable_xiZeta 0
    (fun z hz => xiZeta_ne_zero_of_RH hRH hz)
    (fun z hz => by linarith [re_logDeriv_xiZeta_nonneg hRH hz]) t hσ hσσ'
  simpa using h

end Lindelof
