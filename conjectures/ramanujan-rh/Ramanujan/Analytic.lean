import Ramanujan.Statement
import Ramanujan.LiBounds
import Ramanujan.Poly

/-!
# Ramanujan's inequality for `x ≥ e⁴⁰` from Schoenfeld's bound for `π − li`

`ramanujan_of_schoenfeldPi`: if `|π(x) − li(x)| < √x log x/(8π)` for `x ≥ 2657`
(`Schoenfeld.SchoenfeldPi`), then `π(x)² < (e x/log x) π(x/e)` for every real `x ≥ e⁴⁰`.

With `u = log x ≥ 40` and `y = x/e` (so `log y = u − 1`):

1. `u⁷ ≤ 338 √x` (`growth`): `√x = e²⁰ · e^{u/2−20} ≥ e²⁰ (u/40)⁷` and `40⁷ ≤ 338 e²⁰`.
2. `π(x) < li x + ε(x) ≤ x α(u)/u⁹` (`li_upper` and step 1), `ε(x) = √x log x/(8π)`.
3. `π(y) > li y − ε(y) ≥ y β(u)/(u⁹ (u−1)⁸)` (`li_lower` and step 1).
4. `(x α/u⁹)² < (e x/u) · y β/(u⁹ (u−1)⁸)` is `α² (u−1)⁸ < u⁸ β` (`poly_ineq`).
-/

namespace Ramanujan

open Real

/-- `u⁷ ≤ 338 · e^{u/2}` for `u ≥ 40`. -/
lemma growth {u : ℝ} (hu : 40 ≤ u) : u ^ 7 ≤ 338 * Real.exp (u / 2) := by
  have h1 : u / 40 ≤ Real.exp (u / 40 - 1) := by
    have := Real.add_one_le_exp (u / 40 - 1)
    linarith
  have h2 : (u / 40) ^ 7 ≤ Real.exp (7 * (u / 40 - 1)) := by
    have : Real.exp (u / 40 - 1) ^ 7 = Real.exp (7 * (u / 40 - 1)) := by
      rw [← Real.exp_nat_mul]; norm_num
    rw [← this]
    exact pow_le_pow_left₀ (by linarith) h1 7
  have h3 : Real.exp (7 * (u / 40 - 1)) ≤ Real.exp (u / 2 - 20) :=
    Real.exp_le_exp.mpr (by linarith)
  have h4 : Real.exp (u / 2) = Real.exp 20 * Real.exp (u / 2 - 20) := by
    rw [← Real.exp_add]; ring_nf
  have h5 : (40 : ℝ) ^ 7 ≤ 338 * Real.exp 20 := by
    have he := Real.exp_one_gt_d9
    have : Real.exp 20 = Real.exp 1 ^ 20 := by rw [← Real.exp_nat_mul]; norm_num
    rw [this]
    have : (2.7182818283 : ℝ) ^ 20 ≤ Real.exp 1 ^ 20 := pow_le_pow_left₀ (by norm_num) he.le 20
    nlinarith
  have h6 : u ^ 7 = 40 ^ 7 * (u / 40) ^ 7 := by ring
  rw [h6, h4]
  have hp : 0 ≤ (u / 40) ^ 7 := by positivity
  have hq : 0 ≤ Real.exp (u / 2 - 20) := (Real.exp_pos _).le
  calc (40 : ℝ) ^ 7 * (u / 40) ^ 7 ≤ 338 * Real.exp 20 * (u / 40) ^ 7 :=
        mul_le_mul_of_nonneg_right h5 hp
    _ ≤ 338 * Real.exp 20 * Real.exp (u / 2 - 20) :=
        mul_le_mul_of_nonneg_left (h2.trans h3) (by positivity)
    _ = 338 * (Real.exp 20 * Real.exp (u / 2 - 20)) := by ring

lemma exp_fifteen_le : Real.exp 15 ≤ 3269018 := by
  have he := Real.exp_one_lt_d9
  have : Real.exp 15 = Real.exp 1 ^ 15 := by rw [← Real.exp_nat_mul]; norm_num
  rw [this]
  have : Real.exp 1 ^ 15 ≤ (2.7182818286 : ℝ) ^ 15 :=
    pow_le_pow_left₀ (Real.exp_pos 1).le he.le 15
  linarith [show (2.7182818286 : ℝ) ^ 15 ≤ 3269018 by norm_num]

/-- The error term at `x`: `√x log x/(8π) ≤ 14 x/log⁶ x`. -/
lemma eps_x_le {u s x : ℝ} (hu : 40 ≤ u) (hs0 : 0 < s) (hss : s ^ 2 = x)
    (hg : u ^ 7 ≤ 338 * s) : 1 / (8 * π) * (s * u) ≤ 14 * x / u ^ 6 := by
  have hpi := Real.pi_gt_d2
  have hu0 : 0 < u := by linarith
  rw [← hss, div_mul_eq_mul_div, one_mul, div_le_div_iff₀ (by positivity) (by positivity)]
  have h1 : u ^ 7 * s ≤ 338 * s * s := mul_le_mul_of_nonneg_right hg hs0.le
  have h2 : 338 * (s * s) ≤ 112 * π * (s * s) :=
    mul_le_mul_of_nonneg_right (by linarith) (by positivity)
  calc s * u * u ^ 6 = u ^ 7 * s := by ring
    _ ≤ 338 * s * s := h1
    _ ≤ 112 * π * (s * s) := by linarith
    _ = 14 * s ^ 2 * (8 * π) := by ring

/-- `2e¹⁵ ≤ 9200 x/log⁹ x`. -/
lemma two_a_le {u x : ℝ} (hu : 40 ≤ u) (hx14 : u ^ 14 ≤ 338 ^ 2 * x) :
    2 * Real.exp 15 ≤ 9200 * (x / u ^ 9) := by
  have ha := exp_fifteen_le
  have hu9 : 0 < u ^ 9 := by positivity
  have hu5 : (40 : ℝ) ^ 5 ≤ u ^ 5 := pow_le_pow_left₀ (by norm_num) hu 5
  rw [mul_div_assoc', le_div_iff₀ hu9]
  have h1 : 2 * Real.exp 15 * 338 ^ 2 ≤ 9200 * u ^ 5 := by nlinarith
  have h2 := mul_le_mul_of_nonneg_right h1 hu9.le
  have h3 : 2 * Real.exp 15 * u ^ 9 * 338 ^ 2 ≤ 9200 * (338 ^ 2 * x) := by
    calc 2 * Real.exp 15 * u ^ 9 * 338 ^ 2 = 2 * Real.exp 15 * 338 ^ 2 * u ^ 9 := by ring
      _ ≤ 9200 * u ^ 5 * u ^ 9 := h2
      _ = 9200 * u ^ 14 := by ring
      _ ≤ 9200 * (338 ^ 2 * x) := by linarith
  nlinarith

/-- The error term at `y = x/e`: `√y log y/(8π) ≤ 23 y/log⁶ x`. -/
lemma eps_y_le {u y : ℝ} (hu : 40 ≤ u) (hy0 : 0 < y) (k2 : u ^ 7 ≤ 338 * 1.6488 * √y) :
    1 / (8 * π) * (√y * (u - 1)) ≤ y * (23 * u ^ 3) / u ^ 9 := by
  have hpi := Real.pi_gt_d2
  have hu0 : 0 < u := by linarith
  have hsy0 : 0 < √y := Real.sqrt_pos.mpr hy0
  have hu9 : 0 < u ^ 9 := by positivity
  rw [div_mul_eq_mul_div, one_mul, div_le_div_iff₀ (by positivity) hu9]
  have hyy : y = √y * √y := (Real.mul_self_sqrt hy0.le).symm
  have k1 : (u - 1) * u ^ 9 ≤ u ^ 10 := by nlinarith
  have k3 := mul_le_mul_of_nonneg_left k2 (show 0 ≤ √y * u ^ 3 by positivity)
  have k4 : 338 * 1.6488 * (√y * √y * u ^ 3) ≤ 23 * (8 * π) * (√y * √y * u ^ 3) :=
    mul_le_mul_of_nonneg_right (by nlinarith) (by positivity)
  calc √y * (u - 1) * u ^ 9 = √y * ((u - 1) * u ^ 9) := by ring
    _ ≤ √y * u ^ 10 := mul_le_mul_of_nonneg_left k1 hsy0.le
    _ = √y * u ^ 3 * u ^ 7 := by ring
    _ ≤ √y * u ^ 3 * (338 * 1.6488 * √y) := k3
    _ = 338 * 1.6488 * (√y * √y * u ^ 3) := by ring
    _ ≤ 23 * (8 * π) * (√y * √y * u ^ 3) := k4
    _ = y * (23 * u ^ 3) * (8 * π) := by rw [← hyy]; ring

/-- `e¹⁵ ≤ 12000 y/log⁹ x`, `y = x/e`. -/
lemma a_le_y {u x y : ℝ} (hu : 40 ≤ u) (hx14 : u ^ 14 ≤ 338 ^ 2 * x)
    (hey : Real.exp 1 * y = x) : Real.exp 15 ≤ y * 12000 / u ^ 9 := by
  have ha := exp_fifteen_le
  have he2 := Real.exp_one_lt_d9
  have he0 := Real.exp_pos 1
  have ha0 := Real.exp_pos 15
  have hu9 : 0 < u ^ 9 := by positivity
  have hu5 : (40 : ℝ) ^ 5 ≤ u ^ 5 := pow_le_pow_left₀ (by norm_num) hu 5
  rw [le_div_iff₀ hu9]
  have h0 : Real.exp 15 * Real.exp 1 ≤ 3269018 * 2.7182818286 :=
    mul_le_mul ha he2.le he0.le (by norm_num)
  have h1 : Real.exp 15 * Real.exp 1 * 338 ^ 2 ≤ 12000 * u ^ 5 := by nlinarith
  have h2 := mul_le_mul_of_nonneg_right h1 hu9.le
  have h3 : Real.exp 1 * (Real.exp 15 * u ^ 9) * 338 ^ 2 ≤ Real.exp 1 * (y * 12000) * 338 ^ 2 := by
    calc Real.exp 1 * (Real.exp 15 * u ^ 9) * 338 ^ 2
        = Real.exp 15 * Real.exp 1 * 338 ^ 2 * u ^ 9 := by ring
      _ ≤ 12000 * u ^ 5 * u ^ 9 := h2
      _ = 12000 * u ^ 14 := by ring
      _ ≤ 12000 * (338 ^ 2 * x) := by linarith
      _ = Real.exp 1 * (y * 12000) * 338 ^ 2 := by rw [← hey]; ring
  have h4 := le_of_mul_le_mul_right h3 (by norm_num : (0 : ℝ) < 338 ^ 2)
  exact le_of_mul_le_mul_left h4 he0

/-- The last step: from the two bounds and `poly_ineq`. -/
lemma final_step {u x y P Q : ℝ} (hu : 40 ≤ u) (hx0 : 0 < x) (hey : Real.exp 1 * y = x)
    (hP0 : 0 ≤ P) (hPup : P < x * alpha u / u ^ 9)
    (hQlo : y * beta u / (u ^ 9 * (u - 1) ^ 8) < Q) :
    P ^ 2 < Real.exp 1 * x / u * Q := by
  have hu0 : 0 < u := by linarith
  have hu1 : 0 < u - 1 := by linarith
  have hpoly := poly_ineq hu
  calc P ^ 2 < (x * alpha u / u ^ 9) ^ 2 := pow_lt_pow_left₀ hPup hP0 two_ne_zero
    _ < Real.exp 1 * x / u * (y * beta u / (u ^ 9 * (u - 1) ^ 8)) := by
        rw [← sub_pos]
        have e : Real.exp 1 * x / u * (y * beta u / (u ^ 9 * (u - 1) ^ 8)) -
            (x * alpha u / u ^ 9) ^ 2 =
            x ^ 2 * (u ^ 8 * beta u - alpha u ^ 2 * (u - 1) ^ 8) / (u ^ 18 * (u - 1) ^ 8) := by
          rw [← hey]; field_simp; ring
        rw [e]
        have : 0 < u ^ 8 * beta u - alpha u ^ 2 * (u - 1) ^ 8 := by linarith
        positivity
    _ ≤ Real.exp 1 * x / u * Q := by
        apply mul_le_mul_of_nonneg_left hQlo.le
        have := Real.exp_pos 1
        positivity

/-- **Ramanujan's inequality for `x ≥ e⁴⁰`**, from Schoenfeld's bound `SchoenfeldPi`. -/
theorem ramanujan_of_schoenfeldPi (hS : Schoenfeld.SchoenfeldPi) :
    RamanujanInequalityFrom (Real.exp 40) := by
  intro x hx
  unfold RamanujanAt
  have hx0 : 0 < x := lt_of_lt_of_le (Real.exp_pos 40) hx
  set u := Real.log x with hu_def
  have hu : 40 ≤ u := by
    rw [hu_def, ← Real.log_exp 40]; exact Real.log_le_log (Real.exp_pos 40) hx
  have hxu : x = Real.exp u := (Real.exp_log hx0).symm
  have hu0 : 0 < u := by linarith
  have hu1 : 0 < u - 1 := by linarith
  set s := √x with hs_def
  have hs_eq : s = Real.exp (u / 2) := by rw [hs_def, Real.exp_half, ← hxu]
  have hs0 : 0 < s := by rw [hs_eq]; exact Real.exp_pos _
  have hss : s ^ 2 = x := Real.sq_sqrt hx0.le
  have hg : u ^ 7 ≤ 338 * s := by rw [hs_eq]; exact growth hu
  have hx14 : u ^ 14 ≤ 338 ^ 2 * x := by
    rw [← hss]
    have : (u ^ 7) ^ 2 ≤ (338 * s) ^ 2 := pow_le_pow_left₀ (by positivity) hg 2
    calc u ^ 14 = (u ^ 7) ^ 2 := by ring
      _ ≤ (338 * s) ^ 2 := this
      _ = 338 ^ 2 * s ^ 2 := by ring
  -- the point `y = x/e`
  set y := x / Real.exp 1 with hy_def
  have he0 := Real.exp_pos 1
  have hy0 : 0 < y := div_pos hx0 he0
  have hly : Real.log y = u - 1 := by
    rw [hy_def, Real.log_div hx0.ne' he0.ne', Real.log_exp]
  have hey : Real.exp 1 * y = x := by rw [hy_def]; field_simp
  have h40 : Real.exp 15 * Real.exp 1 ≤ x := by
    rw [← Real.exp_add]; exact le_trans (Real.exp_le_exp.mpr (by norm_num)) hx
  have hx15 : Real.exp 15 ≤ x := le_trans (Real.exp_le_exp.mpr (by norm_num)) hx
  have hy15 : Real.exp 15 ≤ y := by rw [hy_def, le_div_iff₀ he0]; exact h40
  have hbig : (2657 : ℝ) ≤ Real.exp 15 := by
    have h1 : (2 : ℝ) ^ 15 ≤ Real.exp 1 ^ 15 :=
      pow_le_pow_left₀ (by norm_num) (by linarith [Real.exp_one_gt_d9]) 15
    have h2 : Real.exp 1 ^ 15 = Real.exp 15 := by rw [← Real.exp_nat_mul]; norm_num
    linarith [show (2657 : ℝ) ≤ 2 ^ 15 by norm_num]
  -- `√x ≤ 1.6488 √y`
  have hsy : s ≤ 1.6488 * √y := by
    have he2 := Real.exp_one_lt_d9
    have hsy2 : s ^ 2 ≤ (1.6488 * √y) ^ 2 := by
      rw [hss, mul_pow, Real.sq_sqrt hy0.le, ← hey]
      exact mul_le_mul_of_nonneg_right (by linarith) hy0.le
    exact (pow_le_pow_iff_left₀ hs0.le (by positivity) two_ne_zero).mp hsy2
  -- Schoenfeld at `x` and at `y`
  have hSx := hS x (by linarith)
  have hSy := hS y (by linarith)
  rw [← hs_def, ← hu_def] at hSx
  rw [hly] at hSy
  have hSx' := (abs_lt.mp hSx).2
  have hSy' := (abs_lt.mp hSy).1
  -- the upper bound for `π(x)`
  have hliU := li_upper hx15
  rw [← hu_def, A_eq hu0.ne'] at hliU
  have hε1 := eps_x_le hu hs0 hss hg
  have h2a := two_a_le hu hx14
  have hPup : (Nat.primeCounting ⌊x⌋₊ : ℝ) < x * alpha u / u ^ 9 := by
    have e : x * alpha u / u ^ 9 = x * ((u ^ 8 + u ^ 7 + 2 * u ^ 6 + 6 * u ^ 5 + 24 * u ^ 4 +
        120 * u ^ 3 + 720 * u ^ 2 + 5040 * u) / u ^ 9) + 100800 * (x / u ^ 9) +
        9200 * (x / u ^ 9) + 14 * x / u ^ 6 := by
      unfold alpha; field_simp; ring
    rw [e]
    linarith
  -- the lower bound for `π(y)`
  have hliL := li_lower hy15
  rw [hly, A_eq hu1.ne'] at hliL
  have hε2 := eps_y_le hu hy0 (by nlinarith)
  have hae := a_le_y hu hx14 hey
  have hQlo : y * beta u / (u ^ 9 * (u - 1) ^ 8) < (Nat.primeCounting ⌊y⌋₊ : ℝ) := by
    have e : y * beta u / (u ^ 9 * (u - 1) ^ 8) = y * (((u - 1) ^ 8 + (u - 1) ^ 7 +
        2 * (u - 1) ^ 6 + 6 * (u - 1) ^ 5 + 24 * (u - 1) ^ 4 + 120 * (u - 1) ^ 3 +
        720 * (u - 1) ^ 2 + 5040 * (u - 1)) / (u - 1) ^ 9) - y * 12000 / u ^ 9 -
        y * (23 * u ^ 3) / u ^ 9 := by
      unfold beta bnum; field_simp; ring
    rw [e]
    linarith
  exact final_step hu hx0 hey (Nat.cast_nonneg _) hPup hQlo

end Ramanujan
