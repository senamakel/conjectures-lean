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
  -- numerical constants
  have hpi := Real.pi_gt_d2
  have he1 := Real.exp_one_gt_d9
  have he2 := Real.exp_one_lt_d9
  have ha := exp_fifteen_le
  have ha0 := Real.exp_pos 15
  -- `x ≥ u¹⁴ / 338²`
  have hx14 : u ^ 14 ≤ 338 ^ 2 * x := by
    rw [← hss]
    have : (u ^ 7) ^ 2 ≤ (338 * s) ^ 2 := pow_le_pow_left₀ (by positivity) hg 2
    nlinarith
  have hu5 : (40 : ℝ) ^ 5 ≤ u ^ 5 := pow_le_pow_left₀ (by norm_num) hu 5
  have hu9 : 0 < u ^ 9 := by positivity
  -- the point `y = x/e`
  set y := x / Real.exp 1 with hy_def
  have hy0 : 0 < y := div_pos hx0 (Real.exp_pos 1)
  have hly : Real.log y = u - 1 := by
    rw [hy_def, Real.log_div hx0.ne' (Real.exp_pos 1).ne', Real.log_exp]
  have hey : Real.exp 1 * y = x := by rw [hy_def]; field_simp
  have hx_big : (2657 : ℝ) * 3 ≤ x := by
    have := Real.add_one_le_exp 40
    have h3 : (2657 : ℝ) * 3 ≤ 2 ^ 13 := by norm_num
    have h4 : (2 : ℝ) ^ 13 ≤ Real.exp 1 ^ 13 := pow_le_pow_left₀ (by norm_num) (by linarith) 13
    have h5 : Real.exp 1 ^ 13 = Real.exp 13 := by rw [← Real.exp_nat_mul]; norm_num
    have h6 : Real.exp 13 ≤ Real.exp 40 := Real.exp_le_exp.mpr (by norm_num)
    linarith
  have hy_big : (2657 : ℝ) ≤ y := by
    rw [hy_def, le_div_iff₀ (Real.exp_pos 1)]; nlinarith
  have hx15 : Real.exp 15 ≤ x := le_trans (Real.exp_le_exp.mpr (by norm_num)) hx
  have hy15 : Real.exp 15 ≤ y := by
    rw [hy_def, le_div_iff₀ (Real.exp_pos 1), ← Real.exp_add]
    exact le_trans (Real.exp_le_exp.mpr (by norm_num)) hx
  -- `√y ≥ s / 1.6488`
  have hsy : s ≤ 1.6488 * √y := by
    have hsy2 : s ^ 2 ≤ (1.6488 * √y) ^ 2 := by
      rw [hss, mul_pow, Real.sq_sqrt hy0.le, ← hey]
      nlinarith
    exact (pow_le_pow_iff_left₀ hs0.le (by positivity) two_ne_zero).mp hsy2
  -- Schoenfeld at `x` and at `y`
  have hSx := hS x (by linarith)
  have hSy := hS y hy_big
  rw [← hs_def, ← hu_def] at hSx
  rw [hly] at hSy
  have hSx' := (abs_lt.mp hSx).2
  have hSy' := (abs_lt.mp hSy).1
  set P : ℝ := (Nat.primeCounting ⌊x⌋₊ : ℝ) with hP
  set Q : ℝ := (Nat.primeCounting ⌊y⌋₊ : ℝ) with hQ
  have hP0 : 0 ≤ P := Nat.cast_nonneg _
  -- step 2: the upper bound for `π(x)`
  have hliU := li_upper hx15
  rw [← hu_def, A_eq hu0.ne'] at hliU
  have hε1 : 1 / (8 * π) * (s * u) ≤ 14 * x / u ^ 6 := by
    rw [← hss, div_mul_eq_mul_div, one_mul, div_le_div_iff₀ (by positivity) (by positivity)]
    have : u ^ 7 * s ≤ 338 * s * s := mul_le_mul_of_nonneg_right hg hs0.le
    nlinarith
  have h2a : 2 * Real.exp 15 ≤ 9200 * (x / u ^ 9) := by
    rw [mul_div_assoc', le_div_iff₀ hu9]
    have : 2 * Real.exp 15 * 338 ^ 2 ≤ 9200 * 40 ^ 5 := by nlinarith
    have h' : 2 * Real.exp 15 * u ^ 9 * 338 ^ 2 ≤ 9200 * u ^ 14 := by
      have := mul_le_mul_of_nonneg_right
        (show 2 * Real.exp 15 * 338 ^ 2 ≤ 9200 * u ^ 5 by nlinarith) hu9.le
      nlinarith
    nlinarith
  have hPup : P < x * alpha u / u ^ 9 := by
    have e : x * alpha u / u ^ 9 = x * ((u ^ 8 + u ^ 7 + 2 * u ^ 6 + 6 * u ^ 5 + 24 * u ^ 4 +
        120 * u ^ 3 + 720 * u ^ 2 + 5040 * u) / u ^ 9) + 100800 * (x / u ^ 9) +
        9200 * (x / u ^ 9) + 14 * x / u ^ 6 := by
      unfold alpha; field_simp; ring
    rw [e]
    linarith
  -- step 3: the lower bound for `π(y)`
  have hliL := li_lower hy15
  rw [hly, A_eq hu1.ne'] at hliL
  have hε2 : 1 / (8 * π) * (√y * (u - 1)) ≤ y * (23 * u ^ 3) / u ^ 9 := by
    have hsy0 : 0 < √y := Real.sqrt_pos.mpr hy0
    rw [div_mul_eq_mul_div, one_mul, div_le_div_iff₀ (by positivity) hu9]
    have hyy : y = √y * √y := (Real.mul_self_sqrt hy0.le).symm
    have k1 : √y * (u - 1) * u ^ 9 ≤ √y * u ^ 10 := by
      have : (u - 1) * u ^ 9 ≤ u ^ 10 := by nlinarith
      nlinarith
    have k2 : u ^ 7 ≤ 338 * 1.6488 * √y := by nlinarith
    have k3 : √y * u ^ 10 ≤ √y * (338 * 1.6488 * √y) * u ^ 3 := by
      have : u ^ 10 = u ^ 7 * u ^ 3 := by ring
      rw [this]
      have := mul_le_mul_of_nonneg_right k2 (show 0 ≤ u ^ 3 by positivity)
      nlinarith
    rw [hyy]
    nlinarith
  have hae : Real.exp 15 ≤ y * 12000 / u ^ 9 := by
    rw [le_div_iff₀ hu9]
    have : Real.exp 15 * Real.exp 1 * 338 ^ 2 ≤ 12000 * 40 ^ 5 := by nlinarith
    have h' : Real.exp 15 * Real.exp 1 * u ^ 9 * 338 ^ 2 ≤ 12000 * u ^ 14 := by
      have := mul_le_mul_of_nonneg_right
        (show Real.exp 15 * Real.exp 1 * 338 ^ 2 ≤ 12000 * u ^ 5 by nlinarith) hu9.le
      nlinarith
    have : Real.exp 1 * (Real.exp 15 * u ^ 9) ≤ Real.exp 1 * (y * 12000) := by
      rw [show Real.exp 1 * (y * 12000) = 12000 * x by rw [← hey]; ring]
      nlinarith
    exact le_of_mul_le_mul_left this (Real.exp_pos 1)
  have hQlo : y * beta u / (u ^ 9 * (u - 1) ^ 8) < Q := by
    have e : y * beta u / (u ^ 9 * (u - 1) ^ 8) = y * (((u - 1) ^ 8 + (u - 1) ^ 7 +
        2 * (u - 1) ^ 6 + 6 * (u - 1) ^ 5 + 24 * (u - 1) ^ 4 + 120 * (u - 1) ^ 3 +
        720 * (u - 1) ^ 2 + 5040 * (u - 1)) / (u - 1) ^ 9) - y * 12000 / u ^ 9 -
        y * (23 * u ^ 3) / u ^ 9 := by
      unfold beta bnum; field_simp; ring
    rw [e]
    linarith
  -- step 4
  have hpoly := poly_ineq hu
  have hb : 0 < beta u := by
    have : 0 ≤ alpha u ^ 2 * (u - 1) ^ 8 := by positivity
    have h8 : 0 < u ^ 8 := by positivity
    by_contra hcon
    push_neg at hcon
    nlinarith
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
        positivity

end Ramanujan
