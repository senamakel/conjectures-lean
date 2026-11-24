import Cramer.Sharp.Taylor

/-!
# Taylor bounds for `cos` up to degree 10

Continuing `Cramer.Sharp.Taylor` (`cos ≤ T₄`, `sin ≤ T₅`) by the same monotonicity step:

* `cos x ≥ 1 − x²/2 + x⁴/24 − x⁶/720`;
* `sin x ≥ x − x³/6 + x⁵/120 − x⁷/5040` for `x ≥ 0`;
* `cos x ≤ 1 − x²/2 + x⁴/24 − x⁶/720 + x⁸/40320`;
* `sin x ≤ x − x³/6 + x⁵/120 − x⁷/5040 + x⁹/362880` for `x ≥ 0`;
* `cos x ≥ 1 − x²/2 + x⁴/24 − x⁶/720 + x⁸/40320 − x¹⁰/3628800`.

The cosine bounds hold for every real `x` (`cos` is even).
-/

namespace Cramer

open Real

/-- The degree-6 lower Taylor polynomial of `cos`. -/
noncomputable def cosT6 (x : ℝ) : ℝ := 1 - x ^ 2 / 2 + x ^ 4 / 24 - x ^ 6 / 720
/-- The degree-8 upper Taylor polynomial of `cos`. -/
noncomputable def cosT8 (x : ℝ) : ℝ := cosT6 x + x ^ 8 / 40320
/-- The degree-10 lower Taylor polynomial of `cos`. -/
noncomputable def cosT10 (x : ℝ) : ℝ := cosT8 x - x ^ 10 / 3628800

lemma cosT6_le_cos_of_nonneg {x : ℝ} (hx : 0 ≤ x) : cosT6 x ≤ cos x := by
  set G : ℝ → ℝ := fun u => cos u - cosT6 u
  have hG : ∀ u, HasDerivAt G (-sin u + u - u ^ 3 / 6 + u ^ 5 / 120) u := by
    intro u
    have h := (hasDerivAt_cos u).sub (((((hasDerivAt_pow 2 u).div_const 2).const_sub 1).add
      ((hasDerivAt_pow 4 u).div_const 24)).sub ((hasDerivAt_pow 6 u).div_const 720))
    convert h using 1
    · ext v; simp [G, cosT6]
    · push_cast; ring
  have hGd : Differentiable ℝ G := fun u => (hG u).differentiableAt
  have := nonneg_of_deriv_nonneg hGd (by simp [G, cosT6]) (fun u hu => by
    rw [(hG u).deriv]
    have := sin_le_taylor5 hu
    linarith) hx
  simp only [G] at this
  linarith

lemma sin_ge_taylor7 {x : ℝ} (hx : 0 ≤ x) : x - x ^ 3 / 6 + x ^ 5 / 120 - x ^ 7 / 5040 ≤ sin x := by
  set F : ℝ → ℝ := fun u => sin u - (u - u ^ 3 / 6 + u ^ 5 / 120 - u ^ 7 / 5040)
  have hF : ∀ u, HasDerivAt F (cos u - cosT6 u) u := by
    intro u
    have h := (hasDerivAt_sin u).sub ((((hasDerivAt_id' u).sub ((hasDerivAt_pow 3 u).div_const 6)).add
      ((hasDerivAt_pow 5 u).div_const 120)).sub ((hasDerivAt_pow 7 u).div_const 5040))
    convert h using 1
    unfold cosT6; push_cast; ring
  have hFd : Differentiable ℝ F := fun u => (hF u).differentiableAt
  have := nonneg_of_deriv_nonneg hFd (by simp [F]) (fun u hu => by
    rw [(hF u).deriv]
    have := cosT6_le_cos_of_nonneg hu
    linarith) hx
  simp only [F] at this
  linarith

lemma cos_le_cosT8_of_nonneg {x : ℝ} (hx : 0 ≤ x) : cos x ≤ cosT8 x := by
  set G : ℝ → ℝ := fun u => cosT8 u - cos u
  have hG : ∀ u, HasDerivAt G (-u + u ^ 3 / 6 - u ^ 5 / 120 + u ^ 7 / 5040 + sin u) u := by
    intro u
    have h := ((((((hasDerivAt_pow 2 u).div_const 2).const_sub 1).add
      ((hasDerivAt_pow 4 u).div_const 24)).sub ((hasDerivAt_pow 6 u).div_const 720)).add
      ((hasDerivAt_pow 8 u).div_const 40320)).sub (hasDerivAt_cos u)
    convert h using 1
    · ext v; simp [G, cosT8, cosT6]
    · push_cast; ring
  have hGd : Differentiable ℝ G := fun u => (hG u).differentiableAt
  have := nonneg_of_deriv_nonneg hGd (by simp [G, cosT8, cosT6]) (fun u hu => by
    rw [(hG u).deriv]
    have := sin_ge_taylor7 hu
    linarith) hx
  simp only [G] at this
  linarith

lemma sin_le_taylor9 {x : ℝ} (hx : 0 ≤ x) :
    sin x ≤ x - x ^ 3 / 6 + x ^ 5 / 120 - x ^ 7 / 5040 + x ^ 9 / 362880 := by
  set F : ℝ → ℝ := fun u => (u - u ^ 3 / 6 + u ^ 5 / 120 - u ^ 7 / 5040 + u ^ 9 / 362880) - sin u
  have hF : ∀ u, HasDerivAt F (cosT8 u - cos u) u := by
    intro u
    have h := (((((hasDerivAt_id' u).sub ((hasDerivAt_pow 3 u).div_const 6)).add
      ((hasDerivAt_pow 5 u).div_const 120)).sub ((hasDerivAt_pow 7 u).div_const 5040)).add
      ((hasDerivAt_pow 9 u).div_const 362880)).sub (hasDerivAt_sin u)
    convert h using 1
    unfold cosT8 cosT6; push_cast; ring
  have hFd : Differentiable ℝ F := fun u => (hF u).differentiableAt
  have := nonneg_of_deriv_nonneg hFd (by simp [F]) (fun u hu => by
    rw [(hF u).deriv]
    have := cos_le_cosT8_of_nonneg hu
    linarith) hx
  simp only [F] at this
  linarith

lemma cosT10_le_cos_of_nonneg {x : ℝ} (hx : 0 ≤ x) : cosT10 x ≤ cos x := by
  set G : ℝ → ℝ := fun u => cos u - cosT10 u
  have hG : ∀ u, HasDerivAt G
      (-sin u + u - u ^ 3 / 6 + u ^ 5 / 120 - u ^ 7 / 5040 + u ^ 9 / 362880) u := by
    intro u
    have h := (hasDerivAt_cos u).sub ((((((((hasDerivAt_pow 2 u).div_const 2).const_sub 1).add
      ((hasDerivAt_pow 4 u).div_const 24)).sub ((hasDerivAt_pow 6 u).div_const 720)).add
      ((hasDerivAt_pow 8 u).div_const 40320))).sub ((hasDerivAt_pow 10 u).div_const 3628800))
    convert h using 1
    · ext v; simp [G, cosT10, cosT8, cosT6]
    · push_cast; ring
  have hGd : Differentiable ℝ G := fun u => (hG u).differentiableAt
  have := nonneg_of_deriv_nonneg hGd (by simp [G, cosT10, cosT8, cosT6]) (fun u hu => by
    rw [(hG u).deriv]
    have := sin_le_taylor9 hu
    linarith) hx
  simp only [G] at this
  linarith

lemma cosT8_even (x : ℝ) : cosT8 (-x) = cosT8 x := by unfold cosT8 cosT6; ring
lemma cosT10_even (x : ℝ) : cosT10 (-x) = cosT10 x := by unfold cosT10 cosT8 cosT6; ring

/-- `cos x ≤ T₈(x)` for every real `x`. -/
lemma cos_le_cosT8 (x : ℝ) : cos x ≤ cosT8 x := by
  rcases le_total 0 x with h | h
  · exact cos_le_cosT8_of_nonneg h
  · have := cos_le_cosT8_of_nonneg (neg_nonneg.2 h)
    rwa [cos_neg, cosT8_even] at this

/-- `T₁₀(x) ≤ cos x` for every real `x`. -/
lemma cosT10_le_cos (x : ℝ) : cosT10 x ≤ cos x := by
  rcases le_total 0 x with h | h
  · exact cosT10_le_cos_of_nonneg h
  · have := cosT10_le_cos_of_nonneg (neg_nonneg.2 h)
    rwa [cos_neg, cosT10_even] at this

end Cramer
