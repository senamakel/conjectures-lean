import Robin.RH.Psi1
import Robin.Mertens.Identity
import Robin.Main.Tail
import Robin.Main.Gain

/-!
# The analytic estimate for `x ≥ e^{30}`

`ε(x − θ(x)) + Σ_{p≤x} c_p − Σ_{p≤x} min(1/p², ε log p) < γ + log log x`.

By Mertens with remainder (`mertens_RH`), the left side is at most
`γ + log log x + (θ(x) − x)(1/(x log x) − ε) + ∫_x^∞ (t − θ(t)) w(t) dt − gain`.
The second term is `≤ 1.39/(x log x)`, the tail is `≤ (2.32 + …)/(√x log x)` (`tail_bound`) and the
gain is `≥ (2.67 − …)/(√x log x)` (`gain_bound`).
-/

namespace Robin

open Filter Topology Real Chebyshev

/-- `x^{-1/8} ≤ 1/40` for `x ≥ e^{30}`. -/
theorem rpow_neg_eighth_le {x : ℝ} (hx : Real.exp 30 ≤ x) : x ^ (-(1 : ℝ) / 8) ≤ 1 / 40 := by
  have hx0 : 0 < x := lt_of_lt_of_le (Real.exp_pos _) hx
  have h1 : x ^ (-(1 : ℝ) / 8) ≤ (Real.exp 30) ^ (-(1 : ℝ) / 8) :=
    Real.rpow_le_rpow_of_nonpos (Real.exp_pos _) hx (by norm_num)
  rw [← Real.exp_mul] at h1
  have h2 : Real.exp (30 * (-(1 : ℝ) / 8)) = (Real.exp 3.75)⁻¹ := by
    rw [← Real.exp_neg]; norm_num
  rw [h2] at h1
  have he : (40 : ℝ) ≤ Real.exp 3.75 := by
    have h3 : Real.exp 3.75 = Real.exp 1 ^ 3 * Real.exp 0.75 := by
      rw [← Real.exp_nat_mul, ← Real.exp_add]; norm_num
    have he1 := Real.exp_one_gt_d9
    have he2 : 1 + 0.75 + 0.75 ^ 2 / 2 ≤ Real.exp 0.75 := Real.quadratic_le_exp_of_nonneg (by norm_num)
    rw [h3]
    have : (2.7182818283 : ℝ) ^ 3 ≤ Real.exp 1 ^ 3 := by gcongr
    nlinarith
  calc x ^ (-(1 : ℝ) / 8) ≤ (Real.exp 3.75)⁻¹ := h1
    _ ≤ 1 / 40 := by rw [inv_eq_one_div]; exact one_div_le_one_div_of_le (by norm_num) he

theorem main_estimate (hB : Psi1NatBound) {x : ℝ} (hx : Real.exp 30 ≤ x) :
    epsR x * (x - θ x) + primeSum cp x - gainSum x
      < Real.eulerMascheroniConstant + Real.log (Real.log x) := by
  have he30 : (31 : ℝ) ≤ Real.exp 30 := by
    have := Real.add_one_le_exp (30 : ℝ); linarith
  have hx2 : (2 : ℝ) ≤ x := by linarith
  have hx0 : 0 < x := by linarith
  have hL : 30 ≤ Real.log x := by
    rw [← Real.log_exp 30]; exact Real.log_le_log (Real.exp_pos _) hx
  have hL0 : 0 < Real.log x := by linarith
  obtain ⟨-, hM⟩ := mertens_RH (theta_sub_bound hB) hx2
  have hT := tail_bound hB hx
  have hG := gain_bound hB hx
  set L := Real.log x with hLdef
  set I := ∫ t in Set.Ioi x, (θ t - t) * wM t
  -- the boundary term
  have hA : epsR x * (x - θ x) + (θ x - x) / (x * L) ≤ 1.39 / (x * L) := by
    have hlog1 : 1 / (x + 1) ≤ Real.log (1 + 1 / x) := by
      have h := Real.one_sub_inv_le_log_of_pos (show 0 < 1 + 1 / x by positivity)
      have : 1 - (1 + 1 / x)⁻¹ = 1 / (x + 1) := by field_simp; ring
      linarith
    have hlog2 : Real.log (1 + 1 / x) ≤ 1 / x := by
      have := Real.log_le_sub_one_of_pos (show 0 < 1 + 1 / x by positivity); linarith
    have hθ0 := theta_nonneg x
    have hθ4 : θ x ≤ Real.log 4 * x := theta_le_log4_mul_x hx0.le
    have hlog4 : Real.log 4 < 1.39 := by
      have := Real.log_two_lt_d9
      have h4 : Real.log 4 = 2 * Real.log 2 := by
        rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
      linarith
    -- (θ − x)(1/(xL) − ε) with 0 ≤ 1/(xL) − ε ≤ 1/(x² L)
    have heq : epsR x * (x - θ x) + (θ x - x) / (x * L)
        = (θ x - x) * ((1 / x - Real.log (1 + 1 / x)) / L) := by
      unfold epsR; rw [← hLdef]; field_simp; ring
    rw [heq]
    have hd0 : 0 ≤ (1 / x - Real.log (1 + 1 / x)) / L := div_nonneg (by linarith) hL0.le
    have hd1 : (1 / x - Real.log (1 + 1 / x)) / L ≤ 1 / (x ^ 2 * L) := by
      rw [div_le_div_iff₀ hL0 (by positivity)]
      have : 1 / x - 1 / (x + 1) ≤ 1 / x ^ 2 := by
        rw [div_sub_div _ _ hx0.ne' (by linarith : x + 1 ≠ 0), div_le_div_iff₀ (by positivity)
          (by positivity)]
        nlinarith
      have h5 : 1 / x - Real.log (1 + 1 / x) ≤ 1 / x ^ 2 := by linarith
      calc (1 / x - Real.log (1 + 1 / x)) * (x ^ 2 * L) ≤ (1 / x ^ 2) * (x ^ 2 * L) :=
            mul_le_mul_of_nonneg_right h5 (by positivity)
        _ = 1 * L := by field_simp
    calc (θ x - x) * ((1 / x - Real.log (1 + 1 / x)) / L)
        ≤ θ x * ((1 / x - Real.log (1 + 1 / x)) / L) := by nlinarith
      _ ≤ (Real.log 4 * x) * (1 / (x ^ 2 * L)) := by
          apply mul_le_mul hθ4 hd1 hd0 (by positivity)
      _ = Real.log 4 / (x * L) := by field_simp
      _ ≤ 1.39 / (x * L) := by
          apply div_le_div_of_nonneg_right hlog4.le (by positivity)
  -- numerics
  set r := x ^ (-(1 : ℝ) / 8) with hr
  have hr0 : 0 ≤ r := Real.rpow_nonneg hx0.le _
  have hr1 : r ≤ 1 / 40 := rpow_neg_eighth_le hx
  have hr2 : x ^ (-(1 : ℝ) / 4) = r ^ 2 := by
    rw [hr, ← Real.rpow_natCast, ← Real.rpow_mul hx0.le]; norm_num
  have hr4 : r ^ 4 = 1 / √x := by
    rw [hr, ← Real.rpow_natCast, ← Real.rpow_mul hx0.le, Real.sqrt_eq_rpow, one_div,
      ← Real.rpow_neg hx0.le]
    norm_num
  rw [hr2] at hT hG
  have hq : 0 < √x * L := by positivity
  have hA' : 1.39 / (x * L) = 1.39 * r ^ 4 / (√x * L) := by
    have hxs : x = √x * √x := (Real.mul_self_sqrt hx0.le).symm
    have hs0 : 0 < √x := Real.sqrt_pos.mpr hx0
    rw [hr4]; field_simp; rw [Real.sq_sqrt hx0.le]
  have key : 1.39 * r ^ 4 + (2.4 + 3.3 * r + 26 * r ^ 2) < 2.67 - 60 * r ^ 2 := by
    have h2 : r ^ 2 ≤ (1 / 40) ^ 2 := pow_le_pow_left₀ hr0 hr1 2
    have h4 : r ^ 4 ≤ (1 / 40) ^ 4 := pow_le_pow_left₀ hr0 hr1 4
    norm_num at h2 h4
    linarith
  have hfin : 1.39 / (x * L) + (2.4 + 3.3 * r + 26 * r ^ 2) / (√x * L)
      < (2.67 - 60 * r ^ 2) / (√x * L) := by
    rw [hA', ← add_div]
    exact div_lt_div_of_pos_right key hq
  linarith
end Robin
