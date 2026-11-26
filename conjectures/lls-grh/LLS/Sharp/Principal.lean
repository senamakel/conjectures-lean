import LLS.Sharp.Defs
import LLS.L1.Principal
import LLS.L1.Assembly
import LLS.Sharp.Principal.Repr

/-!
# The principal prime sums at full precision (LLS Lemmas 2.4 and 2.6, in the form used)

Write `E(t) = Ψ₁(t) − t²/2`, so `|E(t)| ≤ t^{3/2}/20 + 4t` for `t ≥ 16` (`Robin.psi1_bound`).

* `P2sum x = log x − 1 − γ + E(x)/x² − 2∫_x^∞ E(u) u^{−3} du` (`Principal.Hg_inv_eq`; the
  constant `−1 − γ` comes from the Mellin transform of `Ψ₁` and `−ζ'/ζ(s) − 1/(s−1) → −γ`).
  The error is at most `1/(20√x) + 4/x + 2(1/(10√x) + 4/x) = 0.25/√x + 12/x`.
* `Σ_{n≤x} Λ(n)/(n log n) = K + log log x − 1/log x + ψ(x)/(x log x) + E(x)w(x) + ∫_x^∞ E w'`
  for `x ≥ 100` (`Principal.DA_eq`), and `K ≤ γ` because the sum is at most Mertens'
  `Σ_{p ≤ x} −log(1 − 1/p) = γ + log log x + o(1)`. Combining with the first item,
  `l1Sum1 x = log log x + K − 1 + γ/log x + E(x)w(x) + ∫_x^∞ E w' − ε_P(x)/log x`, and the three
  error terms are at most `(0.0625/√x + 5/x)/log x`, `(0.2875/√x + 11.5/x)/log x` and
  `(0.25/√x + 12/x)/log x`.
-/

namespace LLS.Sharp

open Real Filter Topology MeasureTheory Set Robin Chebyshev
open ArithmeticFunction (vonMangoldt)
open scoped ArithmeticFunction.vonMangoldt
open LLS.Sharp.Principal

lemma rpow_neg_half_eq {x : ℝ} (hx : 0 < x) : x ^ (-(1 : ℝ) / 2) = 1 / √x := by
  rw [show -(1 : ℝ) / 2 = -(1 / 2) by ring, Real.rpow_neg hx.le, ← Real.sqrt_eq_rpow, one_div]

lemma rpow_neg_one_eq {x : ℝ} : x ^ (-(1 : ℝ)) = 1 / x := by
  rw [Real.rpow_neg_one, one_div]

/-- `|∫_x^∞ E u^{−3}| ≤ x^{−1/2}/10 + 4/x` for `x ≥ 16`. -/
lemma abs_tailP_le (hB : Psi1NatBound) {x : ℝ} (hx : 16 ≤ x) :
    |∫ u in Ioi x, fP u| ≤ x ^ (-(1 : ℝ) / 2) / 10 + 4 * x ^ (-(1 : ℝ)) := by
  have hx0 : 0 < x := by linarith
  rw [← integral_qB hx0, ← Real.norm_eq_abs]
  refine norm_integral_le_of_norm_le (integrableOn_qB hx0)
    (ae_restrict_of_forall_mem measurableSet_Ioi fun u (hu : x < u) => ?_)
  have hu0 : 0 < u := by linarith
  rw [Real.norm_eq_abs, fP, abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ u ^ (-(3:ℝ)))]
  exact abs_E1_mul_le hB (by linarith)

/-- `|∫_x^∞ E w'| ≤ (2.875/log x)(x^{−1/2}/10 + 4/x)` for `x ≥ 100`. -/
lemma abs_tailA_le (hB : Psi1NatBound) {x : ℝ} (hx : 100 ≤ x) :
    |∫ u in Ioi x, fA u| ≤ 2.875 / Real.log x * (x ^ (-(1 : ℝ) / 2) / 10 + 4 * x ^ (-(1 : ℝ))) := by
  have hx0 : 0 < x := by linarith
  have hl := LLS.Sharp.Principal.log_ge_four hx
  rw [← integral_qB hx0, ← integral_const_mul, ← Real.norm_eq_abs]
  refine norm_integral_le_of_norm_le ((integrableOn_qB hx0).const_mul _)
    (ae_restrict_of_forall_mem measurableSet_Ioi fun u (hu : x < u) => ?_)
  rw [Real.norm_eq_abs]
  exact abs_fA_le hB (by linarith) hl (Real.log_le_log hx0 hu.le)

lemma abs_E1_div_le (hB : Psi1NatBound) {x : ℝ} (hx : 16 ≤ x) : |E1 x / x ^ 2| ≤ Abd x := by
  have hx0 : 0 < x := by linarith
  rw [abs_div, abs_of_pos (by positivity : (0:ℝ) < x ^ 2), div_le_iff₀ (by positivity)]
  have := E1_le_Abd hB hx
  linarith

lemma abs_E1_wM_le (hB : Psi1NatBound) {x : ℝ} (hx : 100 ≤ x) :
    |E1 x * wM x| ≤ 1.25 / Real.log x * Abd x := by
  have hx0 : 0 < x := by linarith
  have hl := LLS.Sharp.Principal.log_ge_four hx
  set l := Real.log x
  have hw0 : 0 < wM x := wM_pos (by linarith)
  have hw : wM x ≤ 1.25 / (l * x ^ 2) := by
    unfold wM
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have : (1 + l) * l ≤ 1.25 * l ^ 2 := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left this (by positivity : (0:ℝ) ≤ x ^ 2)]
  rw [abs_mul, abs_of_pos hw0]
  calc |E1 x| * wM x ≤ (x ^ 2 * Abd x) * (1.25 / (l * x ^ 2)) :=
        mul_le_mul (E1_le_Abd hB (by linarith)) hw hw0.le (by have := Abd_nonneg hx0; positivity)
    _ = 1.25 / l * Abd x := by field_simp

lemma P2sum_eq_Hg (x : ℕ) (hx : 1 ≤ x) : P2sum x = Hg (fun u => u⁻¹) x := by
  rw [Hg_eq_sum, Nat.floor_natCast, Finset.sum_range_succ, sub_self, mul_zero, add_zero, P2sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  have hx0 : (x : ℝ) ≠ 0 := by exact_mod_cast (show x ≠ 0 by omega)
  field_simp

/-- `|P₂(x) − (log x − 1 − γ)| ≤ 0.25/√x + 12/x`, `x ≥ 16`, in the form used below. -/
lemma Hg_inv_bounds (hB : Psi1NatBound) {x : ℝ} (hx : 16 ≤ x) :
    Hg (fun u => u⁻¹) x = Real.log x - 1 - eulerMascheroniConstant + E1 x / x ^ 2
      - 2 * ∫ u in Ioi x, fP u ∧
    |E1 x / x ^ 2| ≤ x ^ (-(1 : ℝ) / 2) / 20 + 4 * x ^ (-(1 : ℝ)) ∧
    |∫ u in Ioi x, fP u| ≤ x ^ (-(1 : ℝ) / 2) / 10 + 4 * x ^ (-(1 : ℝ)) :=
  ⟨Hg_inv_eq hB (by linarith), abs_E1_div_le hB hx, abs_tailP_le hB hx⟩

/-- `Σ_{n<x} Λ(n)/n (1 − n/x) ≤ log x − 1 − γ + 1/(4√x) + 12/x` (cf. LLS Lemma 2.4). -/
theorem P2sum_le_sharp (hB : Robin.Psi1NatBound) (x : ℕ) (hx : 100 ≤ x) :
    P2sum x ≤ Real.log x - 1 - eulerMascheroniConstant + 0.25 / √(x : ℝ) + 12 / x := by
  have hxR : (100 : ℝ) ≤ x := by exact_mod_cast hx
  have hx0 : (0 : ℝ) < x := by linarith
  obtain ⟨h1, h2, h3⟩ := Hg_inv_bounds hB (x := (x : ℝ)) (by linarith)
  rw [P2sum_eq_Hg x (by omega), h1]
  rw [rpow_neg_half_eq hx0, rpow_neg_one_eq] at h2 h3
  have a1 := (abs_le.mp h2).2
  have a2 := (abs_le.mp h3).1
  have e : 0.25 / √(x : ℝ) + 12 / x = 1 / √(x : ℝ) / 20 + 4 * (1 / x)
      + 2 * (1 / √(x : ℝ) / 10 + 4 * (1 / x)) := by ring
  rw [add_assoc _ (0.25 / √(x : ℝ)), e]
  linarith

/-- The error function in the limit argument for `K ≤ γ`. -/
noncomputable def hErr (x : ℝ) : ℝ :=
  (59 / 11) * x ^ (-(1 / 4 : ℝ)) / Real.log x + (48 / 11) * x ^ (-(1 / 2 : ℝ))
    + (Real.log x)⁻¹ + 1.25 / Real.log x * Abd x
    + 2.875 / Real.log x * (x ^ (-(1 : ℝ) / 2) / 10 + 4 * x ^ (-(1 : ℝ)))

lemma tendsto_rpow_zero {e y : ℝ} (hy : 0 < y) (he : e = -y) :
    Tendsto (fun x : ℝ => x ^ e) atTop (𝓝 0) := he ▸ tendsto_rpow_neg_atTop hy

lemma tendsto_hErr : Tendsto hErr atTop (𝓝 0) := by
  have hlog := Real.tendsto_log_atTop
  have r4 := tendsto_rpow_zero (e := -(1 / 4 : ℝ)) (y := 1 / 4) (by norm_num) rfl
  have r2 := tendsto_rpow_zero (e := -(1 / 2 : ℝ)) (y := 1 / 2) (by norm_num) rfl
  have r2' := tendsto_rpow_zero (e := -(1 : ℝ) / 2) (y := 1 / 2) (by norm_num) (by ring)
  have r1 := tendsto_rpow_zero (e := -(1 : ℝ)) (y := 1) (by norm_num) rfl
  have hA : Tendsto Abd atTop (𝓝 0) := by
    have := (r2'.div_const 20).add (r1.const_mul 4)
    rw [show Abd = fun x => x ^ (-(1:ℝ) / 2) / 20 + 4 * x ^ (-(1:ℝ)) from rfl]
    simpa using this
  have hQ : Tendsto (fun x : ℝ => x ^ (-(1 : ℝ) / 2) / 10 + 4 * x ^ (-(1 : ℝ))) atTop (𝓝 0) := by
    simpa using (r2'.div_const 10).add (r1.const_mul 4)
  have t1 := (r4.const_mul (59 / 11)).div_atTop hlog
  have t2 : Tendsto (fun x : ℝ => (48 / 11) * x ^ (-(1 / 2 : ℝ))) atTop (𝓝 0) := by
    simpa using r2.const_mul (48 / 11)
  have t3 := hlog.inv_tendsto_atTop
  have t4 : Tendsto (fun x : ℝ => 1.25 / Real.log x * Abd x) atTop (𝓝 0) := by
    simpa using ((tendsto_const_nhds (x := (1.25 : ℝ))).div_atTop hlog).mul hA
  have t5 : Tendsto (fun x : ℝ => 2.875 / Real.log x
      * (x ^ (-(1 : ℝ) / 2) / 10 + 4 * x ^ (-(1 : ℝ)))) atTop (𝓝 0) := by
    simpa using ((tendsto_const_nhds (x := (2.875 : ℝ))).div_atTop hlog).mul hQ
  have := (((t1.add t2).add t3).add t4).add t5
  rw [add_zero, add_zero, add_zero, add_zero] at this
  exact this

lemma Hg_gA_le (N : ℕ) :
    Hg gA N ≤ ∑ n ∈ Finset.range (N + 1), (Λ n : ℝ) * (1 / ((n : ℝ) * Real.log n)) := by
  rw [Hg, Nat.floor_natCast]
  have : 0 ≤ ψ (N : ℝ) * gA N := by
    apply mul_nonneg (psi_nonneg _)
    unfold gA
    rcases Nat.eq_zero_or_pos N with h | h
    · simp [h]
    · have : (0 : ℝ) ≤ Real.log N := Real.log_nonneg (by exact_mod_cast h)
      positivity
  simp only [gA] at this ⊢
  linarith

/-- The constant of `Σ Λ(n)/(n log n)` is at most `γ`. -/
lemma DA100_le (hB : Psi1NatBound) : DA 100 ≤ eulerMascheroniConstant := by
  have hlim := tendsto_hErr.comp tendsto_natCast_atTop_atTop
  have hev : ∀ᶠ N : ℕ in atTop, DA 100 - eulerMascheroniConstant ≤ (hErr ∘ Nat.cast) N := by
    filter_upwards [eventually_ge_atTop 100000] with N hN
    have hNR : (100000 : ℝ) ≤ N := by exact_mod_cast hN
    have hDA := DA_eq hB (t := (N : ℝ)) (by linarith)
    have hP := LLS.primeSum_cp_le hB hNR
    have hS := LLS.sum_vonMangoldt_div_log_le N
    have hH := Hg_gA_le N
    have hE := abs_E1_wM_le hB (x := (N : ℝ)) (by linarith)
    have hT := abs_tailA_le hB (x := (N : ℝ)) (by linarith)
    rw [DA] at hDA
    simp only [Function.comp_apply, hErr]
    have := neg_abs_le (E1 (N : ℝ) * wM N)
    have := neg_abs_le (∫ u in Ioi (N : ℝ), fA u)
    linarith
  have := ge_of_tendsto hlim hev
  linarith

/-- `Σ_{n≤x} Λ(n)/(n log n) · log(x/n)/log x ≤ log log x + γ − 1 + γ/log x + (0.6/√x + 29/x)/log x`
(cf. LLS Lemma 2.6). -/
theorem l1Sum1_le_sharp (hB : Robin.Psi1NatBound) (x : ℕ) (hx : 100 ≤ x) :
    l1Sum1 x ≤ Real.log (Real.log x) + eulerMascheroniConstant - 1
      + eulerMascheroniConstant / Real.log x + (0.6 / √(x : ℝ) + 29 / x) / Real.log x := by
  have hxR : (100 : ℝ) ≤ x := by exact_mod_cast hx
  have hx0 : (0 : ℝ) < x := by linarith
  have hl4 := LLS.Sharp.Principal.log_ge_four hxR
  set l := Real.log (x : ℝ) with hl
  have hl0 : 0 < l := by linarith
  obtain ⟨h1, h2, h3⟩ := Hg_inv_bounds hB (x := (x : ℝ)) (by linarith)
  have hDA := DA_eq hB hxR
  have hK := DA100_le hB
  have hE := abs_E1_wM_le hB hxR
  have hT := abs_tailA_le hB hxR
  rw [DA] at hDA
  rw [LLS.l1Sum1_eq x (by omega)]
  have eA : ∑ n ∈ Finset.range (x + 1), (Λ n : ℝ) * (1 / ((n : ℝ) * Real.log n))
      = Hg gA x + ψ (x : ℝ) * gA x := by
    simp only [Hg, gA, Nat.floor_natCast]; ring
  have eB : ∑ n ∈ Finset.range (x + 1), (Λ n : ℝ) / n
      = Hg (fun u => u⁻¹) x + ψ (x : ℝ) * (x : ℝ)⁻¹ := by
    simp only [Hg, Nat.floor_natCast, div_eq_mul_inv]; ring
  rw [eA, eB, h1]
  rw [rpow_neg_half_eq hx0, rpow_neg_one_eq] at h2 h3 hT
  unfold Abd at hE
  rw [rpow_neg_half_eq hx0, rpow_neg_one_eq] at hE
  set a := 1 / √(x : ℝ)
  set b := 1 / (x : ℝ)
  set P := E1 (x : ℝ) / (x : ℝ) ^ 2
  set TP := ∫ u in Ioi (x : ℝ), fP u
  set TA := ∫ u in Ioi (x : ℝ), fA u
  set W := E1 (x : ℝ) * wM x
  have hgA : ψ (x : ℝ) * gA x = 1 / l * (ψ (x : ℝ) * (x : ℝ)⁻¹) := by
    simp only [gA, hl]; field_simp
  -- the error terms
  have hP : -P + 2 * TP ≤ (a / 20 + 4 * b) + 2 * (a / 10 + 4 * b) := by
    have := (abs_le.mp h2).1; have := (abs_le.mp h3).2; linarith
  have hP' : (-P + 2 * TP) / l ≤ ((a / 20 + 4 * b) + 2 * (a / 10 + 4 * b)) / l :=
    div_le_div_of_nonneg_right hP hl0.le
  have hW := (abs_le.mp hE).2
  have hTA := (abs_le.mp hT).2
  have key : W + TA + (-P + 2 * TP) / l ≤ (0.6 * a + 29 * b) / l := by
    have e1 : 1.25 / l * (a / 20 + 4 * b) = (1.25 * (a / 20 + 4 * b)) / l := by ring
    have e2 : 2.875 / l * (a / 10 + 4 * b) = (2.875 * (a / 10 + 4 * b)) / l := by ring
    rw [e1] at hW; rw [e2] at hTA
    have hb : 0 ≤ b := by positivity
    have hsum : (1.25 * (a / 20 + 4 * b)) / l + (2.875 * (a / 10 + 4 * b)) / l
        + ((a / 20 + 4 * b) + 2 * (a / 10 + 4 * b)) / l ≤ (0.6 * a + 29 * b) / l := by
      rw [← add_div, ← add_div]
      exact div_le_div_of_nonneg_right (by linarith) hl0.le
    linarith
  have e3 : 0.6 / √(x : ℝ) + 29 / (x : ℝ) = 0.6 * a + 29 * b := by
    simp only [a, b]; ring
  rw [e3]
  have hKx : Hg gA x = DA 100 - (Real.log x)⁻¹ + Real.log (Real.log x) + W + TA := by
    linarith
  rw [hKx, hgA]
  have e4 : (Real.log (x : ℝ))⁻¹ = 1 / l := by rw [hl, one_div]
  rw [e4]
  have e5 : DA 100 - 1 / l + Real.log l + W + TA + 1 / l * (ψ (x : ℝ) * (x : ℝ)⁻¹)
      - 1 / l * (Real.log (x : ℝ) - 1 - eulerMascheroniConstant + P - 2 * TP
        + ψ (x : ℝ) * (x : ℝ)⁻¹)
      = Real.log l + DA 100 - 1 + eulerMascheroniConstant / l + (W + TA + (-P + 2 * TP) / l) := by
    rw [← hl]; field_simp; ring
  rw [e5]
  linarith

end LLS.Sharp
