import Mathlib

/-!
# Step H: the Riesz and Hardy–Littlewood weights

`W_R(t) = (x/t²) e^{-x/t²}` and `W_H(t) = (1/t) e^{-x/t²}`. With `u = x/t²`,

* `W_R'(t) = -(2x/t³)(1 - u) e^{-u}`, so `|W_R'| ≤ 2x/t³` and `|W_R'| ≤ 16 t/x`;
* `W_H'(t) = (2u - 1) e^{-u}/t²`, so `|W_H'| ≤ 2/t²` and `|W_H'| ≤ 5/x`,

using `(1+u)e^{-u} ≤ 1`, `u²(1+u)e^{-u} ≤ 8`, `(1+2u)e^{-u} ≤ 2`, `u(1+2u)e^{-u} ≤ 5`. The mean
value theorem turns these into bounds on `|W(n+1) - W(n)|`.
-/

namespace Mertens

open Real Set

lemma exp_bound_aux {u c a : ℝ} (h : a ≤ c * Real.exp u) : a * Real.exp (-u) ≤ c := by
  rw [Real.exp_neg, ← div_eq_mul_inv, div_le_iff₀ (Real.exp_pos u)]
  exact h

lemma exp_sq_le {u : ℝ} (hu : 0 ≤ u) : u ^ 2 ≤ 2 * Real.exp u := by
  have := Real.pow_div_factorial_le_exp _ hu 2
  norm_num [Nat.factorial] at this
  linarith

lemma exp_cube_le {u : ℝ} (hu : 0 ≤ u) : u ^ 3 ≤ 6 * Real.exp u := by
  have := Real.pow_div_factorial_le_exp _ hu 3
  norm_num [Nat.factorial] at this
  linarith

lemma one_add_mul_exp_le {u : ℝ} : (1 + u) * Real.exp (-u) ≤ 1 :=
  exp_bound_aux (by linarith [Real.add_one_le_exp u])

lemma sq_one_add_mul_exp_le {u : ℝ} (hu : 0 ≤ u) : u ^ 2 * (1 + u) * Real.exp (-u) ≤ 8 :=
  exp_bound_aux (by nlinarith [exp_sq_le hu, exp_cube_le hu])

lemma one_add_two_mul_exp_le {u : ℝ} : (1 + 2 * u) * Real.exp (-u) ≤ 2 :=
  exp_bound_aux (by linarith [Real.add_one_le_exp u])

lemma mul_one_add_two_mul_exp_le {u : ℝ} (hu : 0 ≤ u) : u * (1 + 2 * u) * Real.exp (-u) ≤ 5 :=
  exp_bound_aux (by nlinarith [exp_sq_le hu, Real.add_one_le_exp u])

/-- The Riesz weight `(x/t²) e^{-x/t²}`. -/
noncomputable def wR (x t : ℝ) : ℝ := x / t ^ 2 * Real.exp (-(x / t ^ 2))

/-- The Hardy–Littlewood weight `(1/t) e^{-x/t²}`. -/
noncomputable def wH (x t : ℝ) : ℝ := 1 / t * Real.exp (-x / t ^ 2)

lemma hasDerivAt_u (x : ℝ) {t : ℝ} (ht : t ≠ 0) :
    HasDerivAt (fun t : ℝ => x / t ^ 2) (-2 * x / t ^ 3) t := by
  have h := ((hasDerivAt_pow 2 t).inv (pow_ne_zero 2 ht)).const_mul x
  convert h using 1
  · funext t; rw [div_eq_mul_inv]; rfl
  · field_simp
    ring

lemma hasDerivAt_wR (x : ℝ) {t : ℝ} (ht : t ≠ 0) :
    HasDerivAt (wR x) (-2 * x / t ^ 3 * (1 - x / t ^ 2) * Real.exp (-(x / t ^ 2))) t := by
  have hu := hasDerivAt_u x ht
  have he := (hu.neg).exp
  simp only [Pi.neg_apply] at he
  have := hu.mul he
  have hfun : wR x = (fun t : ℝ => x / t ^ 2) * fun t => Real.exp (-(x / t ^ 2)) := by
    funext t; rfl
  rw [hfun]
  convert this using 1
  ring

lemma hasDerivAt_wH (x : ℝ) {t : ℝ} (ht : t ≠ 0) :
    HasDerivAt (wH x) ((2 * (x / t ^ 2) - 1) * Real.exp (-(x / t ^ 2)) / t ^ 2) t := by
  have hu := hasDerivAt_u x ht
  have he := (hu.neg).exp
  simp only [Pi.neg_apply] at he
  have hi : HasDerivAt (fun t : ℝ => 1 / t) (-(1 / t ^ 2)) t := by
    have := hasDerivAt_inv ht
    simpa [one_div] using this
  have := hi.mul he
  have hfun : wH x = (fun t : ℝ => 1 / t) * fun t => Real.exp (-(x / t ^ 2)) := by
    funext t; simp only [wH, Pi.mul_apply, neg_div]
  rw [hfun]
  convert this using 1
  field_simp
  ring

/-- Mean value theorem on `[n, n+1]`. -/
lemma abs_sub_le_of_deriv {W W' : ℝ → ℝ} {a C : ℝ}
    (hd : ∀ t ∈ Icc a (a + 1), HasDerivAt W (W' t) t) (hb : ∀ t ∈ Icc a (a + 1), |W' t| ≤ C) :
    |W (a + 1) - W a| ≤ C := by
  have := norm_image_sub_le_of_norm_deriv_le_segment' (f := W) (f' := W')
    (fun t ht => (hd t ht).hasDerivWithinAt) (fun t ht => by
      rw [Real.norm_eq_abs]; exact hb t (Ico_subset_Icc_self ht)) (a + 1) ⟨by linarith, le_rfl⟩
  simpa using this

/-- `|W_R(n+1) - W_R(n)| ≤ 2 x n^{-3}` and `≤ 32 x^{-1} n` for `n ≥ 1`, `x > 0`. -/
lemma wR_diff_le {x : ℝ} (hx : 0 < x) {n : ℕ} (hn : 1 ≤ n) :
    |wR x ((n : ℝ) + 1) - wR x n| ≤ 2 * x ^ (1 : ℝ) * (n : ℝ) ^ (-3 : ℝ) ∧
      |wR x ((n : ℝ) + 1) - wR x n| ≤ 32 * x ^ (-1 : ℝ) * (n : ℝ) ^ (1 : ℝ) := by
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hd : ∀ t ∈ Icc (n : ℝ) (n + 1), HasDerivAt (wR x)
      (-2 * x / t ^ 3 * (1 - x / t ^ 2) * Real.exp (-(x / t ^ 2))) t := fun t ht =>
    hasDerivAt_wR x (by linarith [ht.1])
  have hform : ∀ t : ℝ, 0 < t →
      |-2 * x / t ^ 3 * (1 - x / t ^ 2) * Real.exp (-(x / t ^ 2))| ≤
        2 * x / t ^ 3 * ((1 + x / t ^ 2) * Real.exp (-(x / t ^ 2))) := by
    intro t ht
    have hu : 0 ≤ x / t ^ 2 := by positivity
    rw [abs_mul, abs_mul, abs_of_pos (Real.exp_pos _), abs_div, abs_of_pos (by positivity : 0 < t ^ 3),
      abs_mul, abs_neg, abs_of_pos (by norm_num : (0:ℝ) < 2), abs_of_pos hx]
    have : |1 - x / t ^ 2| ≤ 1 + x / t ^ 2 := by
      rw [abs_le]; constructor <;> linarith
    have := mul_le_mul_of_nonneg_left this (show 0 ≤ 2 * x / t ^ 3 by positivity)
    nlinarith [Real.exp_pos (-(x / t ^ 2))]
  constructor
  · refine abs_sub_le_of_deriv hd fun t ht => ?_
    have ht0 : 0 < t := by linarith [ht.1]
    refine (hform t ht0).trans ?_
    have h1 := one_add_mul_exp_le (u := x / t ^ 2)
    have h2 : 2 * x / t ^ 3 ≤ 2 * x / (n : ℝ) ^ 3 := by
      apply div_le_div_of_nonneg_left (by positivity) (by positivity)
      exact pow_le_pow_left₀ (by positivity) ht.1 3
    have h3 : (2 : ℝ) * x / (n : ℝ) ^ 3 = 2 * x ^ (1 : ℝ) * (n : ℝ) ^ (-3 : ℝ) := by
      rw [Real.rpow_one, Real.rpow_neg (by positivity), div_eq_mul_inv]
      norm_cast
    calc 2 * x / t ^ 3 * ((1 + x / t ^ 2) * Real.exp (-(x / t ^ 2)))
        ≤ 2 * x / t ^ 3 * 1 := by gcongr
      _ ≤ 2 * x / (n : ℝ) ^ 3 := by rw [mul_one]; exact h2
      _ = _ := h3
  · refine abs_sub_le_of_deriv hd fun t ht => ?_
    have ht0 : 0 < t := by linarith [ht.1]
    refine (hform t ht0).trans ?_
    have hu : 0 < x / t ^ 2 := by positivity
    have h1 := sq_one_add_mul_exp_le hu.le
    -- `2x/t³ · (1+u)e^{-u} = (2/t)(1/u²) · u²(1+u)e^{-u} ≤ 16 t/x`
    have heq : 2 * x / t ^ 3 * ((1 + x / t ^ 2) * Real.exp (-(x / t ^ 2))) =
        2 * t / x * ((x / t ^ 2) ^ 2 * (1 + x / t ^ 2) * Real.exp (-(x / t ^ 2))) := by
      field_simp
    rw [heq]
    have h2 : 2 * t / x * ((x / t ^ 2) ^ 2 * (1 + x / t ^ 2) * Real.exp (-(x / t ^ 2))) ≤
        2 * t / x * 8 := mul_le_mul_of_nonneg_left h1 (by positivity)
    have h3 : 2 * t / x * 8 ≤ 32 * x ^ (-1 : ℝ) * (n : ℝ) ^ (1 : ℝ) := by
      rw [Real.rpow_one, Real.rpow_neg_one]
      have : t ≤ 2 * n := by linarith [ht.2]
      rw [div_mul_eq_mul_div, div_le_iff₀ hx]
      field_simp
      nlinarith
    linarith

/-- `|W_H(n+1) - W_H(n)| ≤ 2 n^{-2}` and `≤ 5 x^{-1}` for `n ≥ 1`, `x > 0`. -/
lemma wH_diff_le {x : ℝ} (hx : 0 < x) {n : ℕ} (hn : 1 ≤ n) :
    |wH x ((n : ℝ) + 1) - wH x n| ≤ 2 * x ^ (0 : ℝ) * (n : ℝ) ^ (-2 : ℝ) ∧
      |wH x ((n : ℝ) + 1) - wH x n| ≤ 5 * x ^ (-1 : ℝ) * (n : ℝ) ^ (0 : ℝ) := by
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hd : ∀ t ∈ Icc (n : ℝ) (n + 1), HasDerivAt (wH x)
      ((2 * (x / t ^ 2) - 1) * Real.exp (-(x / t ^ 2)) / t ^ 2) t := fun t ht =>
    hasDerivAt_wH x (by linarith [ht.1])
  have hform : ∀ t : ℝ, 0 < t →
      |(2 * (x / t ^ 2) - 1) * Real.exp (-(x / t ^ 2)) / t ^ 2| ≤
        (1 + 2 * (x / t ^ 2)) * Real.exp (-(x / t ^ 2)) / t ^ 2 := by
    intro t ht
    have hu : 0 ≤ x / t ^ 2 := by positivity
    rw [abs_div, abs_mul, abs_of_pos (Real.exp_pos _), abs_of_pos (by positivity : 0 < t ^ 2)]
    gcongr
    rw [abs_le]; constructor <;> linarith
  constructor
  · refine abs_sub_le_of_deriv hd fun t ht => ?_
    have ht0 : 0 < t := by linarith [ht.1]
    refine (hform t ht0).trans ?_
    have h1 := one_add_two_mul_exp_le (u := x / t ^ 2)
    rw [Real.rpow_zero, mul_one, Real.rpow_neg (by positivity), ← div_eq_mul_inv]
    have : (2 : ℝ) / (n : ℝ) ^ (2 : ℝ) = 2 / (n : ℝ) ^ 2 := by norm_cast
    rw [this]
    calc (1 + 2 * (x / t ^ 2)) * Real.exp (-(x / t ^ 2)) / t ^ 2 ≤ 2 / t ^ 2 := by gcongr
      _ ≤ 2 / (n : ℝ) ^ 2 := by
        apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
        exact pow_le_pow_left₀ (by positivity) ht.1 2
  · refine abs_sub_le_of_deriv hd fun t ht => ?_
    have ht0 : 0 < t := by linarith [ht.1]
    refine (hform t ht0).trans ?_
    have hu : 0 < x / t ^ 2 := by positivity
    have h1 := mul_one_add_two_mul_exp_le hu.le
    rw [Real.rpow_zero, mul_one, Real.rpow_neg_one]
    have heq : (1 + 2 * (x / t ^ 2)) * Real.exp (-(x / t ^ 2)) / t ^ 2 =
        (x / t ^ 2) * (1 + 2 * (x / t ^ 2)) * Real.exp (-(x / t ^ 2)) / x := by
      field_simp
    rw [heq, ← div_eq_mul_inv]
    gcongr

end Mertens
