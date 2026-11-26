import LLS.L1.Assembly

/-!
# `L(1, χ)` bounds of the shape of LLS Theorem 1.5, with weaker constants

LLS Theorem 1.5 (`LLS.L1UpperBound`, `LLS.L1LowerBound` in `LLS/Statement.lean`, unchanged and not
proved here) has `2e^γ(log log q − log 2 + 1/2 + 1/log log q)` and
`(12e^γ/π²)(log log q − log 2 + 1/2 + 1/log log q + 14 log log q/log q)`. We prove, for `q ≥ 10¹⁰`,

* `‖L(1,χ)‖ ≤ 2 e^γ (log log q + C)` and `1/‖L(1,χ)‖ ≤ 2 e^γ (log log q + C)` with `C = 5`.

The leading constant of the upper bound is LLS's; the lower bound has `2e^γ` instead of
`12e^γ/π²` (we do not use LLS Lemma 5.1, the extremality of `χ(p) = −1`), and the additive
constants are weaker (we use a crude bound for the prime-power and principal sums).
-/

namespace LLS

open Erdos985 Erdos985.Analytic
open Real (exp log eulerMascheroniConstant)

/-- Upper bound of LLS Theorem 1.5's shape with additive constant `C`, for `q ≥ 10¹⁰`. -/
def L1UpperBoundWith (C : ℝ) : Prop :=
  ∀ (q : ℕ) [NeZero q], (10 : ℝ) ^ 10 ≤ q → ∀ χ : DirichletCharacter ℂ q, χ.IsPrimitive →
    ‖DirichletCharacter.LFunction χ 1‖ ≤ 2 * exp eulerMascheroniConstant * (log (log q) + C)

/-- Lower bound of LLS Theorem 1.5's shape (leading constant `2e^γ`, LLS: `12e^γ/π²`) with
additive constant `C`, for `q ≥ 10¹⁰`. -/
def L1LowerBoundWith (C : ℝ) : Prop :=
  ∀ (q : ℕ) [NeZero q], (10 : ℝ) ^ 10 ≤ q → ∀ χ : DirichletCharacter ℂ q, χ.IsPrimitive →
    1 / ‖DirichletCharacter.LFunction χ 1‖ ≤ 2 * exp eulerMascheroniConstant * (log (log q) + C)

lemma exp_le_quad {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 1) : Real.exp t ≤ 1 + t + t ^ 2 := by
  have h := Real.exp_bound' h0 h1 (n := 2) (by norm_num)
  simp [Finset.sum_range_succ, Nat.factorial] at h
  nlinarith

variable {N : ℕ} [NeZero N]

/-- The upper bound `log |L(1,χ)| ≤ log l + γ + c/l`, with `c` explicit in `x` and a bound `Zb`
for the zero sum. -/
theorem log_norm_L1_le_c (hGRH : DirichletLNonvanishingRightOfHalf) {χ : DirichletCharacter ℂ N}
    (hprim : χ.IsPrimitive) (hχ : χ ≠ 1) (x : ℕ) (hx : 100000 ≤ x) (Zb : ℝ)
    (hZb : Z2 χ ≤ Zb) :
    Real.log ‖DirichletCharacter.LFunction χ 1‖
      ≤ Real.log (Real.log x) + eulerMascheroniConstant
        + (3 - Real.log x
          + (Real.log x - 1 + 1 / x + Zb * (1 / x + 1 / √(x : ℝ)) - EshiftLo x) / (1 - 1 / x)
          + (-(1 / 2) * Real.log Real.pi - eulerMascheroniConstant / 2)
          + (Zb / √(x : ℝ) + 2 / x) / Real.log x) / Real.log x := by
  have hx2 : 2 ≤ x := by omega
  obtain ⟨hA, hℓ, hU, -⟩ := l1_core hGRH hprim hχ x hx2
  set l := Real.log (x : ℝ)
  set ℓ := (deriv (DirichletCharacter.LFunction χ) 1 / DirichletCharacter.LFunction χ 1).re
  set U := (D χ 1).re
  have hxR : (100000 : ℝ) ≤ x := by exact_mod_cast hx
  have hl : 11 ≤ l := by
    have := Real.log_le_log (by norm_num) hxR
    have h5 : (11 : ℝ) < Real.log 100000 := by
      rw [Real.lt_log_iff_exp_lt (by norm_num)]
      have := Real.exp_one_lt_d9
      calc Real.exp 11 = Real.exp 1 ^ 11 := by rw [← Real.exp_nat_mul]; norm_num
        _ < 2.7182818286 ^ 11 := by gcongr
        _ < 100000 := by norm_num
    linarith
  have hl0 : 0 < l := by linarith
  have hs0 : 0 < √(x : ℝ) := Real.sqrt_pos.2 (by linarith)
  have hax : 0 < 1 - 1 / (x : ℝ) := by
    have : 1 / (x : ℝ) < 1 := by rw [div_lt_one (by linarith)]; linarith
    linarith
  have hZ0 : 0 ≤ Z2 χ := Z2_nonneg χ
  have hc0 : 0 ≤ 1 / (x : ℝ) + 1 / √(x : ℝ) := by positivity
  have hP2 := vonMangoldt_ces_le x hx2
  have hP2' : P2sum x ≤ l - 1 + 1 / x := hP2
  have hA1 := (abs_le.1 (abs_re_l1Sum_le χ x)).2
  have hS1 := l1Sum1_le hGRH x hx
  have hG := (re_gammaLogDeriv_one χ).2
  -- `−U ≤ (…)/(1 − 1/x)`
  have hU' : -U ≤ (l - 1 + 1 / x + Zb * (1 / x + 1 / √(x : ℝ)) - EshiftLo x) / (1 - 1 / x) := by
    rw [le_div_iff₀ hax]
    have : Z2 χ * (1 / x + 1 / √(x : ℝ)) ≤ Zb * (1 / x + 1 / √(x : ℝ)) :=
      mul_le_mul_of_nonneg_right hZb hc0
    linarith
  have hε : (Z2 χ / √(x : ℝ) + 2 / x) / l ^ 2 ≤ ((Zb / √(x : ℝ) + 2 / x) / l) / l := by
    rw [div_div, ← pow_two]
    gcongr
  have habs := (abs_le.1 hA).2
  set M := (l - 1 + 1 / x + Zb * (1 / x + 1 / √(x : ℝ)) - EshiftLo x) / (1 - 1 / x)
  set G1 := -(1 / 2) * Real.log Real.pi - eulerMascheroniConstant / 2
  set E := (Zb / √(x : ℝ) + 2 / x) / l
  have hmain : -ℓ / l ≤ (M + G1) / l := by
    apply div_le_div_of_nonneg_right _ hl0.le
    rw [hℓ]; linarith
  have e : (3 - l + M + G1 + E) / l = 3 / l - 1 + (M + G1) / l + E / l := by
    field_simp
    ring
  rw [e]
  have : ℓ / l = -(-ℓ / l) := by ring
  linarith

/-- The lower bound `−log |L(1,χ)| ≤ log l + γ + c/l`, with `c` explicit in `x` and a bound `Zb`
for the zero sum. -/
theorem neg_log_norm_L1_le_c (hGRH : DirichletLNonvanishingRightOfHalf) {χ : DirichletCharacter ℂ N}
    (hprim : χ.IsPrimitive) (hχ : χ ≠ 1) (x : ℕ) (hx : 100000 ≤ x) (Zb : ℝ)
    (hZb : Z2 χ ≤ Zb) :
    -Real.log ‖DirichletCharacter.LFunction χ 1‖
      ≤ Real.log (Real.log x) + eulerMascheroniConstant
        + (3 - Real.log x
          + (Real.log x - 1 + 1 / x + Zb * (1 / √(x : ℝ) - 1 / x) + Eshift x) / (1 - 1 / x)
          + ((1 / 2) * Real.log Real.pi + eulerMascheroniConstant / 2 + Real.log 2)
          + (Zb / √(x : ℝ) + 2 / x) / Real.log x) / Real.log x := by
  have hx2 : 2 ≤ x := by omega
  obtain ⟨hA, hℓ, -, hU⟩ := l1_core hGRH hprim hχ x hx2
  set l := Real.log (x : ℝ)
  set ℓ := (deriv (DirichletCharacter.LFunction χ) 1 / DirichletCharacter.LFunction χ 1).re
  set U := (D χ 1).re
  have hxR : (100000 : ℝ) ≤ x := by exact_mod_cast hx
  have hl : 11 ≤ l := by
    have := Real.log_le_log (by norm_num) hxR
    have h5 : (11 : ℝ) < Real.log 100000 := by
      rw [Real.lt_log_iff_exp_lt (by norm_num)]
      have := Real.exp_one_lt_d9
      calc Real.exp 11 = Real.exp 1 ^ 11 := by rw [← Real.exp_nat_mul]; norm_num
        _ < 2.7182818286 ^ 11 := by gcongr
        _ < 100000 := by norm_num
    linarith
  have hl0 : 0 < l := by linarith
  have hs0 : 0 < √(x : ℝ) := Real.sqrt_pos.2 (by linarith)
  have hax : 0 < 1 - 1 / (x : ℝ) := by
    have : 1 / (x : ℝ) < 1 := by rw [div_lt_one (by linarith)]; linarith
    linarith
  have hZ0 : 0 ≤ Z2 χ := Z2_nonneg χ
  have hc0 : 0 ≤ 1 / √(x : ℝ) - 1 / (x : ℝ) := by
    have hsx : √(x : ℝ) ≤ x := by
      rw [Real.sqrt_le_left (by linarith)]; nlinarith
    have : 1 / (x : ℝ) ≤ 1 / √(x : ℝ) := one_div_le_one_div_of_le hs0 hsx
    linarith
  have hP2 := vonMangoldt_ces_le x hx2
  have hP2' : P2sum x ≤ l - 1 + 1 / x := hP2
  have hA1 := (abs_le.1 (abs_re_l1Sum_le χ x)).1
  have hP2l := (abs_le.1 (abs_re_cesShift_le χ x)).1
  have hS1 := l1Sum1_le hGRH x hx
  have hG := (re_gammaLogDeriv_one χ).1
  -- `−U ≤ (…)/(1 − 1/x)`
  have hU' : U ≤ (l - 1 + 1 / x + Zb * (1 / √(x : ℝ) - 1 / x) + Eshift x) / (1 - 1 / x) := by
    rw [le_div_iff₀ hax]
    have : Z2 χ * (1 / √(x : ℝ) - 1 / x) ≤ Zb * (1 / √(x : ℝ) - 1 / x) :=
      mul_le_mul_of_nonneg_right hZb hc0
    have hPP : -P2sum x ≥ -(l - 1 + 1 / x) := by linarith
    nlinarith
  have hε : (Z2 χ / √(x : ℝ) + 2 / x) / l ^ 2 ≤ ((Zb / √(x : ℝ) + 2 / x) / l) / l := by
    rw [div_div, ← pow_two]
    gcongr
  have habs := (abs_le.1 hA).1
  set M := (l - 1 + 1 / x + Zb * (1 / √(x : ℝ) - 1 / x) + Eshift x) / (1 - 1 / x)
  set G1 := (1 / 2) * Real.log Real.pi + eulerMascheroniConstant / 2 + Real.log 2
  set E := (Zb / √(x : ℝ) + 2 / x) / l
  have hGG : -G1 ≤ (gammaLogDeriv χ 1).re := by simp only [G1]; linarith
  have hmain : ℓ / l ≤ (M + G1) / l := by
    apply div_le_div_of_nonneg_right _ hl0.le
    rw [hℓ]; linarith
  have e : (3 - l + M + G1 + E) / l = 3 / l - 1 + (M + G1) / l + E / l := by
    field_simp
    ring
  rw [e]
  linarith

end LLS
