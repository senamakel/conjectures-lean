import Mathlib

/-!
# Two elementary Taylor bounds

* `sin x ≤ x − x³/6 + x⁵/120` for `x ≥ 0`;
* `v − v²/2 ≤ log(1 + v)` for `v ≥ 0`.

Both by two (resp. one) monotonicity steps from `Real.sin_ge_sub_cube`.
-/

namespace Cramer

open Real Set

/-- A differentiable function vanishing at `0` with nonnegative derivative on `[0, ∞)` is
nonnegative there. -/
lemma nonneg_of_deriv_nonneg {f : ℝ → ℝ} (hf : Differentiable ℝ f) (h0 : f 0 = 0)
    (hd : ∀ x, 0 ≤ x → 0 ≤ deriv f x) {x : ℝ} (hx : 0 ≤ x) : 0 ≤ f x := by
  have hmono : MonotoneOn f (Ici 0) :=
    monotoneOn_of_deriv_nonneg (convex_Ici 0) hf.continuous.continuousOn
      hf.differentiableOn (fun y hy => by
        rw [interior_Ici] at hy
        exact hd y (le_of_lt hy))
  have := hmono (Set.mem_Ici.mpr le_rfl) (show x ∈ Ici (0 : ℝ) from hx) hx
  rwa [h0] at this

/-- `1 − x²/2 + x⁴/24 − cos x ≥ 0` for `x ≥ 0`. -/
lemma cos_le_taylor4 {x : ℝ} (hx : 0 ≤ x) : cos x ≤ 1 - x ^ 2 / 2 + x ^ 4 / 24 := by
  set G : ℝ → ℝ := fun u => 1 - u ^ 2 / 2 + u ^ 4 / 24 - cos u
  have hG : ∀ u, HasDerivAt G (-u + u ^ 3 / 6 + sin u) u := by
    intro u
    have h2 := ((((hasDerivAt_pow 2 u).div_const 2).const_sub 1).add
      ((hasDerivAt_pow 4 u).div_const 24)).sub (hasDerivAt_cos u)
    exact h2.congr_deriv (by push_cast; ring)
  have hGd : Differentiable ℝ G := fun u => (hG u).differentiableAt
  have := nonneg_of_deriv_nonneg hGd (by simp [G]) (fun u hu => by
    rw [(hG u).deriv]
    have := sin_ge_sub_cube hu
    linarith) hx
  simp only [G] at this
  linarith

/-- `sin x ≤ x − x³/6 + x⁵/120` for `x ≥ 0`. -/
lemma sin_le_taylor5 {x : ℝ} (hx : 0 ≤ x) : sin x ≤ x - x ^ 3 / 6 + x ^ 5 / 120 := by
  set F : ℝ → ℝ := fun u => u - u ^ 3 / 6 + u ^ 5 / 120 - sin u
  have hF : ∀ u, HasDerivAt F (1 - u ^ 2 / 2 + u ^ 4 / 24 - cos u) u := by
    intro u
    have h1 := (((hasDerivAt_id' u).sub ((hasDerivAt_pow 3 u).div_const 6)).add
      ((hasDerivAt_pow 5 u).div_const 120)).sub (hasDerivAt_sin u)
    exact h1.congr_deriv (by push_cast; ring)
  have hFd : Differentiable ℝ F := fun u => (hF u).differentiableAt
  have := nonneg_of_deriv_nonneg hFd (by simp [F]) (fun u hu => by
    rw [(hF u).deriv]
    have := cos_le_taylor4 hu
    linarith) hx
  simp only [F] at this
  linarith

/-- `v − v²/2 ≤ log(1 + v)` for `v ≥ 0`. -/
lemma sub_sq_div_two_le_log {v : ℝ} (hv : 0 ≤ v) : v - v ^ 2 / 2 ≤ Real.log (1 + v) := by
  set g : ℝ → ℝ := fun u => Real.log (1 + u) - u + u ^ 2 / 2
  have hg : ∀ u, 0 ≤ u → HasDerivAt g (1 / (1 + u) - 1 + u) u := by
    intro u hu
    have h1 : HasDerivAt (fun u : ℝ => 1 + u) 1 u := (hasDerivAt_id u).const_add 1
    have h2 := (h1.log (by linarith)).sub (hasDerivAt_id' u)
    have h3 := h2.add ((hasDerivAt_pow 2 u).div_const 2)
    exact h3.congr_deriv (by push_cast; field_simp)
  have hmono : MonotoneOn g (Ici 0) := by
    refine monotoneOn_of_deriv_nonneg (convex_Ici 0) ?_ ?_ ?_
    · intro u hu
      exact (hg u hu).continuousAt.continuousWithinAt
    · intro u hu
      rw [interior_Ici] at hu
      exact (hg u (le_of_lt hu)).differentiableAt.differentiableWithinAt
    · intro u hu
      rw [interior_Ici] at hu
      have hu' : 0 < u := hu
      rw [(hg u hu'.le).deriv]
      have : 1 / (1 + u) - 1 + u = u ^ 2 / (1 + u) := by field_simp; ring
      rw [this]; positivity
  have := hmono (Set.mem_Ici.mpr le_rfl) (show v ∈ Ici (0 : ℝ) from hv) hv
  simp only [g, add_zero, Real.log_one, sub_zero] at this
  norm_num at this
  linarith

end Cramer
