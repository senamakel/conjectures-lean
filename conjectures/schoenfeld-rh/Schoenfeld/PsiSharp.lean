import Schoenfeld.CountSum
import Schoenfeld.Psi

/-!
# `|ψ(x) − x| < √x log² x / (8π)` for `x ≥ 10¹⁰`, under RH and Rosser's zero count

`psi_real_bound` with `h = ⌈4√x⌉`, `F(T) ≤ 2 G(T) ≤ 2 Ub(T)` (`fmin_tsum_le_two_Gsum`,
`Gsum_le_Ub`) and `Ub(T) ≤ log² T/(4π) + (1 − log 2π) log T/(2π) + 0.7` (`Ub_le_quad`) give

`|ψ(x) − x| ≤ √x (u²/(8π) − 0.2435 u + 3.685)`, `u = log x` (`psi_explicit`),

and the linear term is negative enough for `u ≥ 23 log 10 / 10 · 10`, i.e. `x ≥ 10¹⁰`
(`psi_sharp_large`; ratio to `√x u²/(8π)` about `0.90` at `x = 10¹⁰`).
-/

namespace Schoenfeld

open Real Chebyshev

lemma log_pi_lt : Real.log π < 1.1718 := by
  have h1 := Real.log_le_sub_one_of_pos (show 0 < π / 4 by positivity)
  rw [Real.log_div Real.pi_pos.ne' (by norm_num), show (4 : ℝ) = 2 ^ 2 by norm_num,
    Real.log_pow] at h1
  have := Real.pi_lt_d4
  have := log_two_bounds.2
  push_cast at h1
  linarith

lemma log_four_point_four : 1.4772 < Real.log 4.4 ∧ Real.log 4.4 < 1.4864 := by
  have e : Real.log 4.4 = 2 * Real.log 2 + Real.log 1.1 := by
    rw [show (4.4 : ℝ) = 2 ^ 2 * 1.1 by norm_num, Real.log_mul (by norm_num) (by norm_num),
      Real.log_pow]; push_cast; ring
  have h1 := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 1.1 by norm_num)
  have h2 := Real.one_sub_inv_le_log_of_pos (show (0 : ℝ) < 1.1 by norm_num)
  have := log_two_bounds
  constructor
  · rw [e]; norm_num at h2; linarith
  · rw [e]; norm_num at h1; linarith

/-- `Ub(T) ≤ log² T/(4π) + (1 − log 2π) log T/(2π) + 0.7`. -/
lemma Ub_le_quad {T : ℝ} (hT : 4.4 ≤ T) :
    Ub T ≤ Real.log T ^ 2 / (4 * π) + (1 - Real.log (2 * π)) / (2 * π) * Real.log T + 0.65 := by
  have hp := Real.pi_gt_d4
  have hp' := Real.pi_lt_d4
  have hpi : 0 < π := Real.pi_pos
  obtain ⟨hL1, hL2⟩ := log_four_point_four
  have hk1 : 1.8371 < Real.log (2 * π) := by
    rw [Real.log_mul (by norm_num) hpi.ne']
    linarith [log_two_bounds.1, Erdos985.Analytic.PrincipalAux.log_pi_gt']
  have hk2 : Real.log (2 * π) < 1.8650 := by
    rw [Real.log_mul (by norm_num) hpi.ne']
    linarith [log_two_bounds.2, log_pi_lt]
  have e : Ub T = Real.log T ^ 2 / (4 * π) + (1 - Real.log (2 * π)) / (2 * π) * Real.log T
      + (-(Real.log (2 * π) / π) - P1 4.4) - 0.15 / T := by
    have hP : P1 4.4 = Real.log 4.4 ^ 2 / (4 * π) - (Real.log (2 * π) + 1) / (2 * π) * Real.log 4.4
        - (2.463 + 0.3) * (4.4 : ℝ)⁻¹ - 0.3 * (Real.log 4.4 * (4.4 : ℝ)⁻¹) := rfl
    unfold Ub
    rw [hP]
    unfold P1
    generalize Real.log (2 * π) = k
    generalize Real.log 4.4 = L
    generalize Real.log T = ℓ
    field_simp
    ring
  set k := Real.log (2 * π)
  set L := Real.log 4.4
  have hT0 : 0 < T := by linarith
  -- the constant part `−k/π − P1(4.4)`
  have hC : -(k / π) - P1 4.4 ≤ 0.65 := by
    unfold P1
    rw [← sub_nonneg]
    have e : 0.65 - (-(k / π) - (L ^ 2 / (4 * π) - (k + 1) / (2 * π) * L - (2.463 + 0.3) * (4.4 : ℝ)⁻¹
        - 0.3 * (L * (4.4 : ℝ)⁻¹)))
        = (0.65 * π + k + L ^ 2 / 4 - (k + 1) * L / 2 - π * ((2.463 + 0.3) / 4.4) - π * (0.3 * L / 4.4))
          / π := by
      field_simp; ring
    rw [e]
    refine div_nonneg ?_ hpi.le
    have hL0 : 0 < L := by linarith
    have q1 := mul_pos (sub_pos.mpr hk1) (show (0 : ℝ) < 2 - L by linarith)
    have q2 := mul_pos (sub_pos.mpr hp') hL0
    have q3 := mul_pos (sub_pos.mpr hL1) hL0
    ring_nf at q1 q2 q3 ⊢
    linarith
  rw [e]
  have : 0 ≤ 0.15 / T := by positivity
  linarith

/-- `log x ≤ 8 x^{1/8}`, in the form `u² ≤ 64 w` with `w = x^{1/4}`. -/
lemma log_sq_le {x w : ℝ} (hx : 1 ≤ x) (hw : 0 ≤ w) (hwx : w ^ 4 = x) :
    Real.log x ^ 2 ≤ 64 * w := by
  set v := √w with hv
  have hv2 : v ^ 2 = w := Real.sq_sqrt hw
  have hv0 : 0 < v := by
    rw [hv]; apply Real.sqrt_pos.mpr
    by_contra h; push Not at h
    have : w = 0 := le_antisymm h hw
    rw [this] at hwx; norm_num at hwx; linarith
  have hlx : Real.log x = 8 * Real.log v := by
    rw [← hwx, ← hv2, ← pow_mul, Real.log_pow]; push_cast; ring
  have h1 := Real.log_le_sub_one_of_pos hv0
  have h2 : 0 ≤ Real.log x := Real.log_nonneg hx
  have h3 : Real.log x ≤ 8 * v := by rw [hlx]; linarith
  calc Real.log x ^ 2 ≤ (8 * v) ^ 2 := pow_le_pow_left₀ h2 h3 2
    _ = 64 * w := by rw [← hv2]; ring

/-- `2 q(u/2 − 1.0396) ≤ u²/(8π) − 0.2985 u + 1.76`. -/
lemma quad_bound {u ℓ : ℝ} (hu : 0 ≤ u) (hℓ1 : 1 ≤ ℓ) (hℓ : ℓ ≤ u / 2 - 1.0396) :
    2 * (ℓ ^ 2 / (4 * π) + (1 - Real.log (2 * π)) / (2 * π) * ℓ + 0.65)
      ≤ u ^ 2 / (8 * π) - 0.2985 * u + 1.76 := by
  have hp := Real.pi_gt_d4
  have hp' := Real.pi_lt_d4
  have hpi : 0 < π := Real.pi_pos
  have hk1 : 1.8371 < Real.log (2 * π) := by
    rw [Real.log_mul (by norm_num) hpi.ne']
    linarith [log_two_bounds.1, Erdos985.Analytic.PrincipalAux.log_pi_gt']
  have hk2 : Real.log (2 * π) < 1.8650 := by
    rw [Real.log_mul (by norm_num) hpi.ne']
    linarith [log_two_bounds.2, log_pi_lt]
  generalize Real.log (2 * π) = k at hk1 hk2 ⊢
  set m := u / 2 - 1.0396
  have hmono : ℓ ^ 2 + 2 * (1 - k) * ℓ ≤ m ^ 2 + 2 * (1 - k) * m := by
    nlinarith
  rw [← sub_nonneg]
  have e : u ^ 2 / (8 * π) - 0.2985 * u + 1.76 - 2 * (ℓ ^ 2 / (4 * π) + (1 - k) / (2 * π) * ℓ + 0.65)
      = ((m ^ 2 + 2 * (1 - k) * m) - (ℓ ^ 2 + 2 * (1 - k) * ℓ)
        + (u ^ 2 / 4 - 0.597 * π * u + 0.92 * π - m ^ 2 - 2 * (1 - k) * m)) / (2 * π) := by
    field_simp; ring
  rw [e]
  refine div_nonneg ?_ (by positivity)
  have hm : u ^ 2 / 4 - 0.597 * π * u + 0.92 * π - m ^ 2 - 2 * (1 - k) * m
      = u * (k + 1.0396 - 1 - 0.597 * π) + (0.92 * π - 1.0396 ^ 2 - 2 * 1.0396 * (k - 1)) := by
    simp only [m]; ring
  have h1 : 0 ≤ u * (k + 1.0396 - 1 - 0.597 * π) := mul_nonneg hu (by linarith)
  nlinarith

lemma final_arith {s u w A r : ℝ} (hs5 : 100000 ≤ s) (hw2 : w ^ 2 = s) (hw316 : 316 ≤ w)
    (hu64 : u ^ 2 ≤ 64 * w) (hAu : A ≤ u ^ 2 / (8 * π)) (hr : r ≤ 2.8285)
    (hA : A = u ^ 2 / (8 * π) - 0.2985 * u + 1.76) :
    (2 * r * s + 1) / 2 + 3.6 + 0.01 + (s * A + 2.85 * A)
      ≤ s * (u ^ 2 / (8 * π) - 0.2985 * u + 4.62) := by
  have hp := Real.pi_gt_d4
  have h8 : u ^ 2 / (8 * π) ≤ u ^ 2 / 25.13 :=
    div_le_div_of_nonneg_left (sq_nonneg u) (by norm_num) (by linarith)
  have hww : 316 * w ≤ w ^ 2 := by
    nlinarith [mul_nonneg (show (0 : ℝ) ≤ w by linarith) (show (0 : ℝ) ≤ w - 316 by linarith)]
  have hsmall : 2.85 * A ≤ 0.0232 * s := by
    have : u ^ 2 / 25.13 ≤ 64 * w / 25.13 := by gcongr
    have hws : 64 * w ≤ 0.2026 * s := by rw [← hw2]; linarith
    have : 64 * w / 25.13 ≤ 0.2026 * s / 25.13 := by gcongr
    have h11 : 0.2026 * s / 25.13 ≤ 0.00811 * s := by
      rw [div_le_iff₀ (by norm_num)]; nlinarith
    linarith
  have hrs : r * s ≤ 2.8285 * s := mul_le_mul_of_nonneg_right hr (by linarith)
  have e1 : s * A = s * (u ^ 2 / (8 * π)) - 0.2985 * (s * u) + 1.76 * s := by rw [hA]; ring
  have e2 : s * (u ^ 2 / (8 * π) - 0.2985 * u + 4.62)
      = s * (u ^ 2 / (8 * π)) - 0.2985 * (s * u) + 4.62 * s := by ring
  rw [e1, e2]; nlinarith

/-- **`|ψ(x) − x| ≤ √x (log² x/(8π) − 0.2985 log x + 4.62)` for `x ≥ 10¹⁰`**, under RH and
Rosser's zero count. -/
theorem psi_explicit (hRH : RiemannHypothesis) (hR : RosserZeroCount) {x : ℝ}
    (hx : 10 ^ 10 ≤ x) :
    |ψ x - x| ≤ √x * (Real.log x ^ 2 / (8 * π) - 0.2985 * Real.log x + 4.62) := by
  obtain ⟨l2lo, l2hi⟩ := log_two_bounds
  have hpi : 0 < π := Real.pi_pos
  have hp := Real.pi_gt_d4
  have hx0 : 0 < x := by linarith
  set s := √x with hs
  have hs2 : s ^ 2 = x := Real.sq_sqrt hx0.le
  have hs5 : 100000 ≤ s := Real.le_sqrt_of_sq_le (by norm_num; linarith)
  have hs0 : 0 < s := by linarith
  set w := √s with hw
  have hw2 : w ^ 2 = s := Real.sq_sqrt hs0.le
  have hw316 : 316 ≤ w := Real.le_sqrt_of_sq_le (by norm_num; linarith)
  set u := Real.log x with hu
  have hus : Real.log s = u / 2 := by
    rw [hu, ← hs2, Real.log_pow]; push_cast; ring
  have hu64 : u ^ 2 ≤ 64 * w :=
    log_sq_le (by linarith) (by linarith) (by rw [← hs2, ← hw2]; ring)
  have hu0 : 33 * 0.6931471803 ≤ u := by
    have h1 := Real.log_le_log (by norm_num) (show (2 : ℝ) ^ 33 ≤ x by norm_num; linarith)
    rw [Real.log_pow] at h1; push_cast at h1
    linarith
  -- the step `h = ⌈2√8 √x⌉`
  set r := √8 with hr
  have hr2 : r ^ 2 = 8 := Real.sq_sqrt (by norm_num)
  have hr0 : 0 < r := Real.sqrt_pos.mpr (by norm_num)
  have hrlo : 2.8284 ≤ r := Real.le_sqrt_of_sq_le (by norm_num)
  have hrhi : r ≤ 2.8285 := by nlinarith
  set h : ℕ := ⌈2 * r * s⌉₊ with hhdef
  have hh1 : 2 * r * s ≤ h := Nat.le_ceil _
  have hh2 : (h : ℝ) < 2 * r * s + 1 := Nat.ceil_lt_add_one (by positivity)
  have hrs : r * s ≤ 2.8285 * s := mul_le_mul_of_nonneg_right hrhi hs0.le
  have hrs' : 2.8284 * s ≤ r * s := mul_le_mul_of_nonneg_right hrlo hs0.le
  have hss : 100000 * s ≤ s ^ 2 := by nlinarith
  have hh0 : (0 : ℝ) < h := by linarith
  have hh : 1 ≤ h := by exact_mod_cast (show (1 : ℝ) ≤ h by linarith)
  have hB := psi_real_bound hRH x h hh (by linarith)
  set T := 2 * (x + h) / h with hTdef
  have hTeq : T = 2 * x / h + 2 := by rw [hTdef]; field_simp
  have hT1 : T ≤ s / r + 2 := by
    have : 2 * x / h ≤ s / r := by
      rw [div_le_div_iff₀ hh0 hr0, ← hs2]
      have := mul_le_mul_of_nonneg_left hh1 (show 0 ≤ s by linarith)
      nlinarith
    linarith
  have hT2 : s / 3 ≤ T := by
    have : s / 3 ≤ 2 * x / h := by
      rw [le_div_iff₀ hh0, ← hs2]
      have := mul_le_mul_of_nonneg_left hh2.le (show 0 ≤ s by linarith)
      nlinarith
    linarith
  have hTpos : 0 < T := by linarith
  have hT44 : 4.4 ≤ T := by linarith
  -- `F(T) ≤ 2 Ub(T) ≤ u²/(8π) − 0.24 u + 1.7`
  have hF := (fmin_tsum_le_two_Gsum hRH hTpos.le).trans
    (mul_le_mul_of_nonneg_left ((Gsum_le_Ub hRH hR hT44).trans (Ub_le_quad hT44)) (by norm_num))
  have hlr : Real.log r = 3 / 2 * Real.log 2 := by
    rw [hr, Real.log_sqrt (by norm_num), show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]
    push_cast; ring
  have hlT : Real.log T ≤ u / 2 - 1.0396 := by
    have h1 := Real.log_le_sub_one_of_pos (show 0 < T / (s / r) by positivity)
    rw [Real.log_div hTpos.ne' (by positivity), Real.log_div hs0.ne' hr0.ne', hus, hlr] at h1
    have : T / (s / r) - 1 ≤ 0.00006 := by
      rw [div_sub_one (by positivity), div_le_iff₀ (by positivity)]
      have : T - s / r ≤ 2 := by linarith
      have : 35000 ≤ s / r := by rw [le_div_iff₀ hr0]; linarith
      linarith
    linarith
  have hlT1 : 1 ≤ Real.log T := by
    rw [← Real.log_exp 1]
    exact Real.log_le_log (Real.exp_pos 1) (by linarith [Real.exp_one_lt_d9])
  have hq := quad_bound (u := u) (by linarith) hlT1 hlT
  have hF0 : 0 ≤ ∑' ρ, fmin T ρ := tsum_nonneg (fmin_nonneg hTpos.le)
  set A := u ^ 2 / (8 * π) - 0.2985 * u + 1.76 with hA
  have hFA : ∑' ρ, fmin T ρ ≤ A := hF.trans hq
  have hA0 : 0 ≤ A := hF0.trans hFA
  have hAu : A ≤ u ^ 2 / (8 * π) := by rw [hA]; linarith
  have hsq : √(x + h) ≤ s + 2.85 := by
    rw [show s + 2.85 = √((s + 2.85) ^ 2) from (Real.sqrt_sq (by linarith)).symm]
    have e : (s + 2.85) ^ 2 = s ^ 2 + 5.7 * s + 8.1225 := by ring
    have hle : x + h ≤ (s + 2.85) ^ 2 := by rw [e, hs2]; linarith
    exact Real.sqrt_le_sqrt hle
  have hz : √(x + h) * ∑' ρ, fmin T ρ ≤ (s + 2.85) * A :=
    mul_le_mul hsq hFA hF0 (by linarith)
  have hh3 : 1.5 / (h : ℝ) ≤ 0.01 := by rw [div_le_iff₀ hh0]; linarith
  calc |ψ x - x| ≤ h / 2 + 3.6 + 1.5 / h + √(x + h) * ∑' ρ, fmin T ρ := hB
    _ ≤ (2 * r * s + 1) / 2 + 3.6 + 0.01 + (s * A + 2.85 * A) := by
        have : (s + 2.85) * A = s * A + 2.85 * A := by ring
        linarith
    _ ≤ s * (u ^ 2 / (8 * π) - 0.2985 * u + 4.62) := final_arith hs5 hw2 hw316 hu64 hAu hrhi hA

/-- **`|ψ(x) − x| < √x log² x/(8π)` for `x ≥ 10¹⁰`**, under RH and Rosser's zero count. -/
theorem psi_sharp_large (hRH : RiemannHypothesis) (hR : RosserZeroCount) {x : ℝ}
    (hx : 10 ^ 10 ≤ x) :
    |ψ x - x| < 1 / (8 * π) * (√x * Real.log x ^ 2) := by
  have h := psi_explicit hRH hR hx
  have hu0 : 33 * 0.6931471803 ≤ Real.log x := by
    have h1 := Real.log_le_log (by norm_num) (show (2 : ℝ) ^ 33 ≤ x by norm_num; linarith)
    rw [Real.log_pow] at h1; push_cast at h1
    linarith [log_two_bounds.1]
  have hs : 0 < √x := Real.sqrt_pos.mpr (by linarith)
  have : √x * (Real.log x ^ 2 / (8 * π) - 0.2985 * Real.log x + 4.62)
      < 1 / (8 * π) * (√x * Real.log x ^ 2) := by
    have e : 1 / (8 * π) * (√x * Real.log x ^ 2) = √x * (Real.log x ^ 2 / (8 * π)) := by ring
    rw [e]
    apply mul_lt_mul_of_pos_left _ hs
    linarith
  linarith

end Schoenfeld
