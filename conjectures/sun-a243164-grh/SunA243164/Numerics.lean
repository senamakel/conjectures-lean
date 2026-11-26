import SunA243164.Analytic
import Erdos985.Numerics

/-!
# The sieve numerics: `SieveNumerics (10^8)`

For every prime `P ≥ 10^8` we exhibit an admissible sieving set `S` with `SieveIneq P S`.
Write `F = (P - 1).primeFactors`, `ω = |F|`, `x = π(P)`, `s = √x`, `L = log P`.

*Analytic inputs* (all unconditional, `analytic_facts`):
* `x log P ≥ P log 2` (Mathlib's `Chebyshev.pi_ge_of_four_le`), hence `s ≥ s₀` for `P ≥ P₀`;
* `x < P`, so `log x < L`;
* `Epp x ≤ 2 log 2 · s + 2 L s / c₃` (`Sieve.Epp_le` and `x^{1/3} ≤ s / c₃` once `c₃³ ≤ s`);
* `c(P, x) s L ≤ (2/3)(1 + 2/s₀ + 3/s₀³)(L + 5/3) s + L + 2` (the definition of `bachC`).

*Choice of `S`.* For `ω ≤ 14`, `S = {ℓ ∈ F : ℓ ≥ 5}` and `E = F \ S ⊆ {2, 3}`; `2 ∈ E` always.
If `|S| ≤ M`, the exchange lemma `sum_inv_le` gives `Σ_{ℓ ∈ S} 1/ℓ ≤ Σ` of the reciprocals of
the first `M` primes `≥ 5`, so `δ_S ≥ δ_M`. For `ω ≥ 15`, `S = ∅` and
`(2^ω / θ_F)^4 ≤ C (P - 1)` with `C = ∏_{p < 23} 16 p³/(p - 1)⁴ < 517576` (`D_pow4_le`).

*Lower bounds for `P` from `ω`* (`mul_prod_le`, via erdos-985's
`pow_card_primeFactors_mul_le`): `ω ≥ 9 ⇒ P > 2·3⋯23`, `ω ≥ 10 ⇒ P > 2·3⋯29`,
`ω ≥ 15 ⇒ P > 2·3⋯47`.

*The real cores* `core_sieve` and `core_nosieve` reduce `SieveIneq` to a polynomial inequality
in `L = log P₀ + u` against `P = P₀ e^u`, closed by `1 + t ≤ e^t` factor by factor: no
monotonicity argument and no calculus are needed. All the remaining checks are rational
arithmetic discharged by `norm_num`.

| case | `P₀` | `e = |E|` | `|S| ≤` | `4 U₀ B² / (P₀ log 2)` |
|---|---|---|---|---|
| `ω ≤ 8` | `10^8` | 1 | 7 | 0.322 |
| `ω ≤ 8` | `10^8` | 2 | 6 | 0.754 |
| `ω = 9` | `223092871` | 1 | 8 | 0.259 |
| `ω = 9` | `223092871` | 2 | 7 | 0.643 |
| `10 ≤ ω ≤ 14` | `6469693231` | 1 | 13 | 0.112 |
| `10 ≤ ω ≤ 14` | `6469693231` | 2 | 12 | 0.300 |
| `ω ≥ 15`, no sieve | `614889782588491411` | — | — | 0.039 |

The last column is the ratio that must be `< 1`; the tightest case is `ω ≤ 8`, `3 ∣ P - 1`.
-/

namespace SunA243164.Numerics

open Real Finset ArithmeticFunction
open SunA243164 SunA243164.Sieve

/-! ## Elementary real lemmas -/

lemma lin_le_exp {B c u : ℝ} (hB : 0 < B) : B + c * u ≤ B * exp (c / B * u) := by
  have h := Real.add_one_le_exp (c / B * u)
  have e : B + c * u = B * (c / B * u + 1) := by field_simp; ring
  rw [e]
  exact mul_le_mul_of_nonneg_left h hB.le

/-- The sieve case, as a statement about real numbers. -/
lemma core_sieve (P0 U0 s0 c3 dt0 K0 a0 a1 : ℝ) {P s L u Epp csl dt K : ℝ}
    (hs0 : 0 < s0) (hc3 : 0 < c3) (hdt0 : 0 < dt0) (hU0 : 0 < U0) (hK0 : 0 ≤ K0)
    (ha0n : 0 ≤ a0)
    (ha1 : 2 / (c3 * dt0) + K0 * (2 / 3 * (1 + 2 / s0 + 3 / s0 ^ 3) + 1 / s0) ≤ a1)
    (ha0 : 2 * 0.6931471808 / dt0 + 1 / 20 + 3 / s0
      + K0 * (10 / 9 * (1 + 2 / s0 + 3 / s0 ^ 3) + 2 / s0) ≤ a0)
    (hB : 4 * U0 * (a0 + a1 * U0) ^ 2 < P0 * 0.6931471803)
    (hB' : 1 / U0 + 2 * a1 / (a0 + a1 * U0) ≤ 1)
    (hs : s0 ≤ s) (hπ : P * 0.6931471803 ≤ s ^ 2 * L) (hLpos : 0 < L)
    (hLU : L ≤ U0 + u) (hu : 0 ≤ u) (hPe : P = P0 * exp u)
    (hE : Epp ≤ 2 * 0.6931471808 * s + 2 * L * s / c3) (hE0 : 0 ≤ Epp)
    (hc0 : 0 ≤ csl) (hc : csl ≤ 2 / 3 * (1 + 2 / s0 + 3 / s0 ^ 3) * (L + 5 / 3) * s + L + 2)
    (hdt : dt0 ≤ dt) (hK : K ≤ K0) :
    Epp < dt * (s ^ 2 / 2 - (s / 20 + 3) - K * csl) := by
  set g := 1 + 2 / s0 + 3 / s0 ^ 3 with hg
  have hspos : 0 < s := lt_of_lt_of_le hs0 hs
  have hgpos : 0 < g := by positivity
  have ha1pos : 0 < a1 := lt_of_lt_of_le (by positivity) ha1
  set A := a0 + a1 * L with hA
  -- (a) everything but the main term is at most `s · A`
  have hlin : Epp / dt0 + s / 20 + 3 + K0 * csl ≤ s * A := by
    have h1 : Epp / dt0 ≤ s * (2 * 0.6931471808 / dt0) + s * L * (2 / (c3 * dt0)) := by
      rw [div_le_iff₀ hdt0]
      have e : (s * (2 * 0.6931471808 / dt0) + s * L * (2 / (c3 * dt0))) * dt0
          = 2 * 0.6931471808 * s + 2 * L * s / c3 := by field_simp
      rw [e]; exact hE
    have h3 : (3 : ℝ) ≤ s * (3 / s0) := by
      rw [mul_div_assoc', le_div_iff₀ hs0]; linarith
    have h4 : L + 2 ≤ s * ((L + 2) / s0) := by
      rw [mul_div_assoc', le_div_iff₀ hs0]
      have := mul_le_mul_of_nonneg_left hs (by linarith : (0 : ℝ) ≤ L + 2)
      linarith
    have h5 : K0 * csl ≤ K0 * (2 / 3 * g * (L + 5 / 3) * s + s * ((L + 2) / s0)) :=
      mul_le_mul_of_nonneg_left (by linarith) hK0
    have e : s * (2 * 0.6931471808 / dt0) + s * L * (2 / (c3 * dt0)) + s / 20 + s * (3 / s0)
        + K0 * (2 / 3 * g * (L + 5 / 3) * s + s * ((L + 2) / s0))
        = s * ((2 * 0.6931471808 / dt0 + 1 / 20 + 3 / s0 + K0 * (10 / 9 * g + 2 / s0))
          + (2 / (c3 * dt0) + K0 * (2 / 3 * g + 1 / s0)) * L) := by ring
    have h6 : s * ((2 * 0.6931471808 / dt0 + 1 / 20 + 3 / s0 + K0 * (10 / 9 * g + 2 / s0))
          + (2 / (c3 * dt0) + K0 * (2 / 3 * g + 1 / s0)) * L) ≤ s * A := by
      apply mul_le_mul_of_nonneg_left _ hspos.le
      have := mul_le_mul_of_nonneg_right ha1 hLpos.le
      linarith
    linarith
  -- (b) `2 A < s`
  set B := a0 + a1 * U0 with hBdef
  have hBpos : 0 < B := by positivity
  have hA0 : 0 ≤ A := add_nonneg ha0n (mul_nonneg ha1pos.le hLpos.le)
  have hAle : A ≤ B * exp (a1 / B * u) := by
    calc A ≤ B + a1 * u := by
          have := mul_le_mul_of_nonneg_left hLU ha1pos.le
          rw [hA, hBdef]; linarith
      _ ≤ _ := lin_le_exp hBpos
  have hLle : L ≤ U0 * exp (1 / U0 * u) := by
    have := lin_le_exp (c := 1) (u := u) hU0
    rw [one_mul] at this
    exact hLU.trans this
  have hpoly : 4 * L * A ^ 2 < P * 0.6931471803 := by
    have hexp : exp (1 / U0 * u) * exp (a1 / B * u) ^ 2 ≤ exp u := by
      rw [sq, ← Real.exp_add, ← Real.exp_add]
      apply Real.exp_le_exp.mpr
      have e : 1 / U0 * u + (a1 / B * u + a1 / B * u) = (1 / U0 + 2 * a1 / B) * u := by ring
      rw [e]
      exact mul_le_of_le_one_left hu hB'
    calc 4 * L * A ^ 2 ≤ 4 * (U0 * exp (1 / U0 * u)) * (B * exp (a1 / B * u)) ^ 2 := by
          gcongr
      _ = 4 * U0 * B ^ 2 * (exp (1 / U0 * u) * exp (a1 / B * u) ^ 2) := by ring
      _ ≤ 4 * U0 * B ^ 2 * exp u := by gcongr
      _ < P0 * 0.6931471803 * exp u := mul_lt_mul_of_pos_right hB (Real.exp_pos u)
      _ = P * 0.6931471803 := by rw [hPe]; ring
  have hsq : (2 * A) ^ 2 < s ^ 2 := by
    have h1 : 4 * A ^ 2 * L < s ^ 2 * L := by
      have e : 4 * A ^ 2 * L = 4 * L * A ^ 2 := by ring
      rw [e]; exact lt_of_lt_of_le hpoly hπ
    have h2 := lt_of_mul_lt_mul_right h1 hLpos.le
    calc (2 * A) ^ 2 = 4 * A ^ 2 := by ring
      _ < s ^ 2 := h2
  have h2A : 2 * A < s := lt_of_pow_lt_pow_left₀ 2 hspos.le hsq
  have hsA : s * A < s ^ 2 / 2 := by
    have := mul_lt_mul_of_pos_left h2A hspos
    linarith
  -- (c) conclusion
  have hX : Epp / dt0 < s ^ 2 / 2 - (s / 20 + 3) - K * csl := by
    have : K * csl ≤ K0 * csl := mul_le_mul_of_nonneg_right hK hc0
    linarith
  have hX0 : 0 ≤ s ^ 2 / 2 - (s / 20 + 3) - K * csl := le_trans (div_nonneg hE0 hdt0.le) hX.le
  rw [div_lt_iff₀ hdt0] at hX
  calc Epp < (s ^ 2 / 2 - (s / 20 + 3) - K * csl) * dt0 := hX
    _ ≤ dt * (s ^ 2 / 2 - (s / 20 + 3) - K * csl) := by
      rw [mul_comm]; exact mul_le_mul_of_nonneg_right hdt hX0

/-- The case without sieve, as a statement about real numbers: `D = T / θ`, `D⁴ ≤ C P`. -/
lemma core_nosieve (P0 U0 s0 c3 Cq b0 b1 η : ℝ) {P s L u Epp csl θ T : ℝ}
    (hP0 : 0 < P0) (hs0 : 0 < s0) (hc3 : 0 < c3) (hU0 : 0 < U0) (hb0n : 0 ≤ b0) (hη : 0 < η)
    (hCq : 0 ≤ Cq)
    (hb1 : 2 / c3 + 2 / 3 * (1 + 2 / s0 + 3 / s0 ^ 3) + 1 / s0 ≤ b1)
    (hb0 : 2 * 0.6931471808 + 10 / 9 * (1 + 2 / s0 + 3 / s0 ^ 3) + 2 / s0 ≤ b0)
    (hη' : η ≤ 1 / 2 - (1 / 20 + 3 / s0) / s0)
    (hQ : Cq * U0 ^ 2 * (b0 + b1 * U0) ^ 4 < η ^ 4 * 0.6931471803 ^ 2 * P0)
    (hQ' : 2 / U0 + 4 * b1 / (b0 + b1 * U0) ≤ 1)
    (hs : s0 ≤ s) (hπ : P * 0.6931471803 ≤ s ^ 2 * L) (hLpos : 0 < L)
    (hLU : L ≤ U0 + u) (hu : 0 ≤ u) (hPe : P = P0 * exp u)
    (hE : Epp ≤ 2 * 0.6931471808 * s + 2 * L * s / c3) (hE0 : 0 ≤ Epp)
    (hc0 : 0 ≤ csl) (hc : csl ≤ 2 / 3 * (1 + 2 / s0 + 3 / s0 ^ 3) * (L + 5 / 3) * s + L + 2)
    (hθ0 : 0 < θ) (hθ1 : θ ≤ 1) (hT : 1 ≤ T) (hD : (T / θ) ^ 4 ≤ Cq * P) :
    Epp < θ * (s ^ 2 / 2 - (s / 20 + 3) - (T - 1) * csl) := by
  set g := 1 + 2 / s0 + 3 / s0 ^ 3 with hg
  have hspos : 0 < s := lt_of_lt_of_le hs0 hs
  have hgpos : 0 < g := by positivity
  have hb1pos : 0 < b1 := lt_of_lt_of_le (by positivity) hb1
  have hPpos : 0 < P := by rw [hPe]; positivity
  set D := T / θ with hDdef
  have hDT : T ≤ D := le_div_self (by linarith) hθ0 hθ1
  have hDθ : 1 / θ ≤ D := div_le_div_of_nonneg_right hT hθ0.le
  have hDpos : 0 < D := lt_of_lt_of_le (by linarith) hDT
  set Q := b0 + b1 * L with hQdef
  have hQpos : 0 < Q := by positivity
  have hsum : Epp + csl ≤ s * Q := by
    have h4 : L + 2 ≤ s * ((L + 2) / s0) := by
      rw [mul_div_assoc', le_div_iff₀ hs0]
      have := mul_le_mul_of_nonneg_left hs (by linarith : (0 : ℝ) ≤ L + 2)
      linarith
    have e : 2 * 0.6931471808 * s + 2 * L * s / c3 + (2 / 3 * g * (L + 5 / 3) * s
        + s * ((L + 2) / s0))
        = s * ((2 * 0.6931471808 + 10 / 9 * g + 2 / s0) + (2 / c3 + 2 / 3 * g + 1 / s0) * L) := by
      field_simp; ring
    have h6 : s * ((2 * 0.6931471808 + 10 / 9 * g + 2 / s0) + (2 / c3 + 2 / 3 * g + 1 / s0) * L)
        ≤ s * Q := by
      apply mul_le_mul_of_nonneg_left _ hspos.le
      have := mul_le_mul_of_nonneg_right hb1 hLpos.le
      linarith
    linarith
  set Bq := b0 + b1 * U0 with hBqdef
  have hBq : 0 < Bq := by positivity
  have hQle : Q ≤ Bq * exp (b1 / Bq * u) := by
    calc Q ≤ Bq + b1 * u := by
          have := mul_le_mul_of_nonneg_left hLU hb1pos.le
          rw [hQdef, hBqdef]; linarith
      _ ≤ _ := lin_le_exp hBq
  have hLle : L ≤ U0 * exp (1 / U0 * u) := by
    have := lin_le_exp (c := 1) (u := u) hU0
    rw [one_mul] at this
    exact hLU.trans this
  have hpoly : Cq * Q ^ 4 * L ^ 2 < η ^ 4 * 0.6931471803 ^ 2 * P := by
    have hexp : exp (b1 / Bq * u) ^ 4 * exp (1 / U0 * u) ^ 2 ≤ exp u := by
      rw [← Real.exp_nat_mul, ← Real.exp_nat_mul, ← Real.exp_add]
      apply Real.exp_le_exp.mpr
      push_cast
      have e : 4 * (b1 / Bq * u) + 2 * (1 / U0 * u) = (2 / U0 + 4 * b1 / Bq) * u := by ring
      rw [e]
      exact mul_le_of_le_one_left hu hQ'
    calc Cq * Q ^ 4 * L ^ 2
        ≤ Cq * (Bq * exp (b1 / Bq * u)) ^ 4 * (U0 * exp (1 / U0 * u)) ^ 2 := by gcongr
      _ = Cq * U0 ^ 2 * Bq ^ 4 * (exp (b1 / Bq * u) ^ 4 * exp (1 / U0 * u) ^ 2) := by ring
      _ ≤ Cq * U0 ^ 2 * Bq ^ 4 * exp u := by gcongr
      _ < η ^ 4 * 0.6931471803 ^ 2 * P0 * exp u := mul_lt_mul_of_pos_right hQ (Real.exp_pos u)
      _ = η ^ 4 * 0.6931471803 ^ 2 * P := by rw [hPe]; ring
  have h4 : (D * Q) ^ 4 < (η * s) ^ 4 := by
    have hL2 : 0 < L ^ 2 := by positivity
    have h1 : (D * Q) ^ 4 * L ^ 2 ≤ Cq * P * Q ^ 4 * L ^ 2 := by
      rw [mul_pow]
      have : D ^ 4 * Q ^ 4 ≤ Cq * P * Q ^ 4 := mul_le_mul_of_nonneg_right hD (by positivity)
      exact mul_le_mul_of_nonneg_right this hL2.le
    have h2 : Cq * P * Q ^ 4 * L ^ 2 < η ^ 4 * (P * 0.6931471803) ^ 2 := by
      have := mul_lt_mul_of_pos_left hpoly hPpos
      calc Cq * P * Q ^ 4 * L ^ 2 = P * (Cq * Q ^ 4 * L ^ 2) := by ring
        _ < P * (η ^ 4 * 0.6931471803 ^ 2 * P) := this
        _ = η ^ 4 * (P * 0.6931471803) ^ 2 := by ring
    have h3 : η ^ 4 * (P * 0.6931471803) ^ 2 ≤ (η * s) ^ 4 * L ^ 2 := by
      have hP' : 0 ≤ P * 0.6931471803 := by positivity
      have : (P * 0.6931471803) ^ 2 ≤ (s ^ 2 * L) ^ 2 := pow_le_pow_left₀ hP' hπ 2
      calc η ^ 4 * (P * 0.6931471803) ^ 2 ≤ η ^ 4 * (s ^ 2 * L) ^ 2 := by gcongr
        _ = (η * s) ^ 4 * L ^ 2 := by ring
    have := lt_of_le_of_lt h1 (lt_of_lt_of_le h2 h3)
    exact lt_of_mul_lt_mul_right this hL2.le
  have hDQ : D * Q < η * s := lt_of_pow_lt_pow_left₀ 4 (by positivity) h4
  have hfin : D * (Epp + csl) < s ^ 2 / 2 - (s / 20 + 3) := by
    have h1 : D * (Epp + csl) ≤ s * (D * Q) := by
      have := mul_le_mul_of_nonneg_left hsum hDpos.le
      linarith
    have h2 : s * (D * Q) < s * (η * s) := mul_lt_mul_of_pos_left hDQ hspos
    have hκ : 0 ≤ 1 / 20 + 3 / s0 := by positivity
    have h3 : s * (η * s) ≤ s ^ 2 / 2 - (1 / 20 + 3 / s0) / s0 * s ^ 2 := by
      have := mul_le_mul_of_nonneg_left hη' (sq_nonneg s)
      linarith
    have h5 : (1 / 20 + 3 / s0) * s ≤ (1 / 20 + 3 / s0) / s0 * s ^ 2 := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hs0]
      have := mul_le_mul_of_nonneg_left hs (mul_nonneg hκ hspos.le)
      linarith
    have h6 : s / 20 + 3 ≤ (1 / 20 + 3 / s0) * s := by
      have : (3 : ℝ) ≤ 3 / s0 * s := by
        rw [div_mul_eq_mul_div, le_div_iff₀ hs0]; linarith
      linarith
    linarith
  have hX : Epp / θ < s ^ 2 / 2 - (s / 20 + 3) - (T - 1) * csl := by
    have h1 : Epp / θ ≤ D * Epp := by
      rw [div_eq_mul_one_div, mul_comm]
      exact mul_le_mul_of_nonneg_right hDθ hE0
    have h2 : (T - 1) * csl ≤ D * csl := mul_le_mul_of_nonneg_right (by linarith) hc0
    linarith
  rw [div_lt_iff₀ hθ0] at hX
  linarith

/-! ## The analytic inputs at `x = π(P)` -/

lemma log_le_mul_of_le {P0 P : ℝ} (hP0 : 0 < P0) (h : P0 ≤ P) (h1 : 1 ≤ Real.log P0) :
    Real.log P ≤ Real.log P0 * (P / P0) := by
  have hP : 0 < P := by linarith
  have ht := Erdos985.log_le_tangent P P0 hP hP0
  have ht1 : 1 ≤ P / P0 := (one_le_div hP0).mpr h
  nlinarith [mul_nonneg (sub_nonneg.2 ht1) (sub_nonneg.2 h1)]

lemma one_le_log_of_eight_le {P0 : ℕ} (h : 8 ≤ P0) : 1 ≤ Real.log P0 := by
  have h1 : Real.log 8 ≤ Real.log P0 := Real.log_le_log (by norm_num) (by exact_mod_cast h)
  have h8 : Real.log 8 = 3 * Real.log 2 := by
    rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]; norm_num
  linarith [Real.log_two_gt_d9]

/-- `log P₀ ≤ k log 2 + P₀/2^k - 1` (tangent line at `2^k`). -/
lemma log_le_U (P0 k : ℕ) (hP0 : 0 < P0) :
    Real.log P0 ≤ k * 0.6931471808 + P0 / 2 ^ k - 1 := by
  have h := Erdos985.log_le_tangent (P0 : ℝ) (2 ^ k) (by exact_mod_cast hP0) (by positivity)
  rw [Real.log_pow] at h
  have := Real.log_two_lt_d9
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  nlinarith

lemma Epp_nonneg (x : ℕ) : 0 ≤ Epp x := by
  unfold Epp
  refine Finset.sum_nonneg fun n hn => ?_
  have hnx := Finset.mem_range.mp hn
  have hx0 : (0 : ℝ) < x := by exact_mod_cast (by omega : 0 < x)
  have h1 : (n : ℝ) / x ≤ 1 := by
    rw [div_le_one hx0]; exact_mod_cast hnx.le
  have h0 : (0 : ℝ) ≤ (if n.Prime then 0 else 1) := by split_ifs <;> norm_num
  exact mul_nonneg (mul_nonneg vonMangoldt_nonneg (by linarith)) h0

lemma Epp_bound {P x : ℕ} (hx2 : 2 ≤ x) (hxP : x ≤ P) {s0 c3 : ℝ} (hc3 : 0 < c3)
    (hc3' : c3 ^ 3 ≤ s0) (hs : s0 ≤ √(x : ℝ)) :
    Epp x ≤ 2 * 0.6931471808 * √(x : ℝ) + 2 * Real.log P * √(x : ℝ) / c3 := by
  have h := Epp_le x hx2
  set s := √(x : ℝ) with hsdef
  have hxR : (2 : ℝ) ≤ x := by exact_mod_cast hx2
  have hxP' : (x : ℝ) ≤ P := by exact_mod_cast hxP
  have hspos : 0 < s := Real.sqrt_pos.2 (by linarith)
  have hs2 : s ^ 2 = x := Real.sq_sqrt (by linarith)
  have hl2p : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hfl : (⌊Real.log x / Real.log 2⌋₊ : ℝ) ≤ Real.log P / Real.log 2 := by
    refine (Nat.floor_le (div_nonneg (Real.log_nonneg (by linarith)) hl2p.le)).trans ?_
    gcongr
  have hcube : (x : ℝ) ^ ((1 : ℝ) / 3) ≤ s / c3 := by
    set r := (x : ℝ) ^ ((1 : ℝ) / 3) with hr
    have hr0 : 0 ≤ r := by positivity
    have hr3 : r ^ 3 = x := by
      rw [hr, ← Real.rpow_natCast, ← Real.rpow_mul (by linarith)]; norm_num
    by_contra hcon
    push_neg at hcon
    have h1 : (s / c3) ^ 3 < r ^ 3 := pow_lt_pow_left₀ hcon (by positivity) (by norm_num)
    rw [hr3, div_pow, div_lt_iff₀ (by positivity)] at h1
    have h2 : (x : ℝ) * c3 ^ 3 ≤ s ^ 2 * s := by
      rw [hs2]; exact mul_le_mul_of_nonneg_left (hc3'.trans hs) (by linarith)
    nlinarith
  have hlog4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
  have hLP : 0 ≤ Real.log P := Real.log_nonneg (by linarith)
  calc Epp x ≤ Real.log 4 * (s + (⌊Real.log x / Real.log 2⌋₊ : ℝ) * (x : ℝ) ^ ((1 : ℝ) / 3)) := h
    _ ≤ Real.log 4 * (s + (Real.log P / Real.log 2) * (s / c3)) := by
      have : (⌊Real.log x / Real.log 2⌋₊ : ℝ) * (x : ℝ) ^ ((1 : ℝ) / 3)
          ≤ (Real.log P / Real.log 2) * (s / c3) :=
        mul_le_mul hfl hcube (by positivity) (by positivity)
      have := Real.log_nonneg (show (1 : ℝ) ≤ 4 by norm_num)
      gcongr
    _ = 2 * Real.log 2 * s + 2 * Real.log P * s / c3 := by
      rw [hlog4]; field_simp
    _ ≤ 2 * 0.6931471808 * s + 2 * Real.log P * s / c3 := by
      have := Real.log_two_lt_d9
      nlinarith

lemma csl_bound {P x : ℕ} (hx2 : 2 ≤ x) (hxP : x ≤ P) {s0 : ℝ} (hs0 : 0 < s0)
    (hs : s0 ≤ √(x : ℝ)) :
    0 ≤ Erdos985.bachC P x * √(x : ℝ) * Real.log P ∧
    Erdos985.bachC P x * √(x : ℝ) * Real.log P
      ≤ 2 / 3 * (1 + 2 / s0 + 3 / s0 ^ 3) * (Real.log P + 5 / 3) * √(x : ℝ)
        + Real.log P + 2 := by
  set s := √(x : ℝ) with hsdef
  have hxR : (2 : ℝ) ≤ x := by exact_mod_cast hx2
  have hxP' : (x : ℝ) ≤ P := by exact_mod_cast hxP
  have hspos : 0 < s := Real.sqrt_pos.2 (by linarith)
  have hs2 : (x : ℝ) = s ^ 2 := (Real.sq_sqrt (by linarith)).symm
  have hx32 : (x : ℝ) ^ (3 / 2 : ℝ) = s ^ 3 := by
    rw [hs2, show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add (by positivity),
      Real.rpow_one, ← Real.sqrt_eq_rpow, Real.sqrt_sq hspos.le]
    ring
  have hLpos : 0 < Real.log P := Real.log_pos (by linarith)
  have hlx0 : 0 ≤ Real.log x := Real.log_nonneg (by linarith)
  have hlx : Real.log x ≤ Real.log P := Real.log_le_log (by linarith) hxP'
  have hexp : Erdos985.bachC P x * s * Real.log P
      = 2 / 3 * (1 + 2 / s + 3 / s ^ 3) * (Real.log P + 5 / 3) * s + (Real.log x + 2) := by
    unfold Erdos985.bachC
    rw [← hsdef, hx32]
    field_simp
  rw [hexp]
  have hG : 1 + 2 / s + 3 / s ^ 3 ≤ 1 + 2 / s0 + 3 / s0 ^ 3 := by
    have : 2 / s ≤ 2 / s0 := by gcongr
    have : 3 / s ^ 3 ≤ 3 / s0 ^ 3 := by gcongr
    linarith
  constructor
  · positivity
  · have : 2 / 3 * (1 + 2 / s + 3 / s ^ 3) * (Real.log P + 5 / 3) * s
        ≤ 2 / 3 * (1 + 2 / s0 + 3 / s0 ^ 3) * (Real.log P + 5 / 3) * s := by gcongr
    linarith

/-- Lower bound for `π(P)` and the relation `x log P ≥ P log 2`. -/
lemma primeCounting_facts {P0 P : ℕ} (hP0 : 8 ≤ P0) (hP : P0 ≤ P) {U0 : ℝ}
    (hU0 : Real.log P0 ≤ U0) :
    (P0 : ℝ) * 0.6931471803 / U0 ≤ Nat.primeCounting P ∧
      (P : ℝ) * 0.6931471803 ≤ Nat.primeCounting P * Real.log P := by
  have h4 : 4 ≤ P := by omega
  have hpi := Chebyshev.pi_ge_of_four_le h4
  have hL1 : 1 ≤ Real.log P0 := one_le_log_of_eight_le hP0
  have hP0R : (0 : ℝ) < P0 := by exact_mod_cast (by omega : 0 < P0)
  have hPR : (P0 : ℝ) ≤ P := by exact_mod_cast hP
  have hPpos : (0 : ℝ) < P := by linarith
  have hLP : 0 < Real.log P := Real.log_pos (by exact_mod_cast (by omega : 1 < P))
  have h2 : (P : ℝ) * Real.log 2 ≤ Nat.primeCounting P * Real.log P := (div_le_iff₀ hLP).mp hpi
  have h2' : (P : ℝ) * 0.6931471803 ≤ Nat.primeCounting P * Real.log P := by
    have := Real.log_two_gt_d9
    nlinarith
  refine ⟨?_, h2'⟩
  have hU0pos : 0 < U0 := by linarith
  have hLle : Real.log P ≤ U0 * (P / P0) := by
    have := log_le_mul_of_le hP0R hPR hL1
    have h' : Real.log P0 * (P / P0) ≤ U0 * (P / P0) :=
      mul_le_mul_of_nonneg_right hU0 (by positivity)
    linarith
  have hx0 : (0 : ℝ) ≤ Nat.primeCounting P := Nat.cast_nonneg _
  have h3 : (P : ℝ) * 0.6931471803 ≤ Nat.primeCounting P * (U0 * (P / P0)) :=
    h2'.trans (mul_le_mul_of_nonneg_left hLle hx0)
  rw [div_le_iff₀ hU0pos]
  have e : (Nat.primeCounting P : ℝ) * (U0 * (P / P0)) = (Nat.primeCounting P * U0) * P / P0 := by
    ring
  rw [e, le_div_iff₀ hP0R] at h3
  nlinarith

/-! ## From the real cores to `SieveIneq` -/

/-- **Sieve case.** The numerical hypotheses are rational arithmetic. -/
theorem sieveIneq_of (P0 : ℕ) (U0 s0 c3 dt0 K0 a0 a1 : ℝ) (hP08 : 8 ≤ P0)
    (hU0 : Real.log P0 ≤ U0) (hs0 : 0 < s0) (hs0' : s0 ^ 2 ≤ P0 * 0.6931471803 / U0)
    (hc3 : 0 < c3) (hc3' : c3 ^ 3 ≤ s0) (hdt0 : 0 < dt0) (hK0 : 0 ≤ K0) (ha0n : 0 ≤ a0)
    (ha1 : 2 / (c3 * dt0) + K0 * (2 / 3 * (1 + 2 / s0 + 3 / s0 ^ 3) + 1 / s0) ≤ a1)
    (ha0 : 2 * 0.6931471808 / dt0 + 1 / 20 + 3 / s0
      + K0 * (10 / 9 * (1 + 2 / s0 + 3 / s0 ^ 3) + 2 / s0) ≤ a0)
    (hB : 4 * U0 * (a0 + a1 * U0) ^ 2 < P0 * 0.6931471803)
    (hB' : 1 / U0 + 2 * a1 / (a0 + a1 * U0) ≤ 1)
    {P : ℕ} (hP : P0 ≤ P) (S : Finset ℕ)
    (hdt : dt0 ≤ deltaOf S * θ ((P - 1).primeFactors \ S)) (hK : sieveK P S ≤ K0) :
    SieveIneq P S := by
  obtain ⟨hxlow, hπ⟩ := primeCounting_facts hP08 hP hU0
  set x := Nat.primeCounting P with hxdef
  have hL1 : 1 ≤ Real.log P0 := one_le_log_of_eight_le hP08
  have hU0pos : 0 < U0 := by linarith
  have hP0R : (0 : ℝ) < P0 := by exact_mod_cast (by omega : 0 < P0)
  have hPR : (P0 : ℝ) ≤ P := by exact_mod_cast hP
  have hx0 : (0 : ℝ) ≤ x := Nat.cast_nonneg _
  have hs : s0 ≤ √(x : ℝ) := Real.le_sqrt_of_sq_le (hs0'.trans hxlow)
  have hxP : x ≤ P := (primeCounting_lt_self (by omega)).le
  have hx2 : 2 ≤ x := by
    have : Nat.primeCounting 8 ≤ x := Nat.monotone_primeCounting (by omega)
    have h8 : Nat.primeCounting 8 = 4 := by decide
    omega
  have hs2 : (x : ℝ) = √(x : ℝ) ^ 2 := (Real.sq_sqrt hx0).symm
  have hLpos : 0 < Real.log P := by
    have := Real.log_le_log hP0R hPR; linarith
  have hLge : Real.log P0 ≤ Real.log P := Real.log_le_log hP0R hPR
  have hPe : (P : ℝ) = P0 * exp (Real.log P - Real.log P0) := by
    rw [Real.exp_sub, Real.exp_log (by linarith), Real.exp_log hP0R]; field_simp
  obtain ⟨hc0, hc⟩ := csl_bound hx2 hxP hs0 hs
  have hE := Epp_bound hx2 hxP hc3 hc3' hs
  have key := core_sieve (P0 : ℝ) U0 s0 c3 dt0 K0 a0 a1 hs0 hc3 hdt0 hU0pos hK0 ha0n ha1 ha0 hB hB'
    hs (by rw [← hs2]; exact hπ) hLpos (by linarith) (by linarith) hPe hE (Epp_nonneg x) hc0 hc
    hdt hK
  rw [← hs2] at key
  simp only [SieveIneq]
  exact key

/-- **Case without sieve** (`S = ∅`). -/
theorem sieveIneq_empty_of (P0 : ℕ) (U0 s0 c3 Cq b0 b1 η : ℝ) (hP08 : 8 ≤ P0)
    (hU0 : Real.log P0 ≤ U0) (hs0 : 0 < s0) (hs0' : s0 ^ 2 ≤ P0 * 0.6931471803 / U0)
    (hc3 : 0 < c3) (hc3' : c3 ^ 3 ≤ s0) (hb0n : 0 ≤ b0) (hη : 0 < η) (hCq : 0 ≤ Cq)
    (hb1 : 2 / c3 + 2 / 3 * (1 + 2 / s0 + 3 / s0 ^ 3) + 1 / s0 ≤ b1)
    (hb0 : 2 * 0.6931471808 + 10 / 9 * (1 + 2 / s0 + 3 / s0 ^ 3) + 2 / s0 ≤ b0)
    (hη' : η ≤ 1 / 2 - (1 / 20 + 3 / s0) / s0)
    (hQ : Cq * U0 ^ 2 * (b0 + b1 * U0) ^ 4 < η ^ 4 * 0.6931471803 ^ 2 * P0)
    (hQ' : 2 / U0 + 4 * b1 / (b0 + b1 * U0) ≤ 1)
    {P : ℕ} (hP : P0 ≤ P)
    (hD : ((2 : ℝ) ^ (P - 1).primeFactors.card / θ (P - 1).primeFactors) ^ 4 ≤ Cq * P) :
    SieveIneq P ∅ := by
  obtain ⟨hxlow, hπ⟩ := primeCounting_facts hP08 hP hU0
  set x := Nat.primeCounting P with hxdef
  have hL1 : 1 ≤ Real.log P0 := one_le_log_of_eight_le hP08
  have hU0pos : 0 < U0 := by linarith
  have hP0R : (0 : ℝ) < P0 := by exact_mod_cast (by omega : 0 < P0)
  have hPR : (P0 : ℝ) ≤ P := by exact_mod_cast hP
  have hx0 : (0 : ℝ) ≤ x := Nat.cast_nonneg _
  have hs : s0 ≤ √(x : ℝ) := Real.le_sqrt_of_sq_le (hs0'.trans hxlow)
  have hxP : x ≤ P := (primeCounting_lt_self (by omega)).le
  have hx2 : 2 ≤ x := by
    have : Nat.primeCounting 8 ≤ x := Nat.monotone_primeCounting (by omega)
    have h8 : Nat.primeCounting 8 = 4 := by decide
    omega
  have hs2 : (x : ℝ) = √(x : ℝ) ^ 2 := (Real.sq_sqrt hx0).symm
  have hLpos : 0 < Real.log P := by
    have := Real.log_le_log hP0R hPR; linarith
  have hLge : Real.log P0 ≤ Real.log P := Real.log_le_log hP0R hPR
  have hPe : (P : ℝ) = P0 * exp (Real.log P - Real.log P0) := by
    rw [Real.exp_sub, Real.exp_log (by linarith), Real.exp_log hP0R]; field_simp
  obtain ⟨hc0, hc⟩ := csl_bound hx2 hxP hs0 hs
  have hE := Epp_bound hx2 hxP hc3 hc3' hs
  set F := (P - 1).primeFactors with hF
  have hθ0 : 0 < θ F :=
    Finset.prod_pos fun ℓ hℓ => aR_pos (Nat.prime_of_mem_primeFactors hℓ).two_le
  have hθ1 : θ F ≤ 1 := by
    refine Finset.prod_le_one₀ (fun ℓ hℓ => (aR_pos (Nat.prime_of_mem_primeFactors hℓ).two_le).le)
      fun ℓ _ => ?_
    unfold aR
    have : (0 : ℝ) ≤ 1 / (ℓ : ℝ) := by positivity
    linarith
  have hT : (1 : ℝ) ≤ 2 ^ F.card := one_le_pow₀ (by norm_num)
  have key := core_nosieve (P0 : ℝ) U0 s0 c3 Cq b0 b1 η hP0R hs0 hc3 hU0pos hb0n hη hCq hb1 hb0
    hη' hQ hQ' hs (by rw [← hs2]; exact hπ) hLpos (by linarith) (by linarith) hPe hE
    (Epp_nonneg x) hc0 hc hθ0 hθ1 hT hD
  have hδ : deltaOf ∅ = 1 := by simp [deltaOf]
  have hK : sieveK P ∅ = 2 ^ F.card - 1 := by
    simp only [sieveK, hδ, Finset.card_empty, Nat.sub_zero, Nat.cast_zero]; ring
  rw [← hs2] at key
  simp only [SieveIneq]
  rw [hK, hδ, Finset.sdiff_empty, one_mul]
  exact key

/-! ## Combinatorics of the prime factors of `P - 1` -/

/-- The exchange lemma: a set of at most `|G|` integers, each outside `G` larger than every
element of `G`, has reciprocal sum at most that of `G`. -/
lemma sum_inv_le (S G : Finset ℕ) (B : ℕ) (hG : ∀ g ∈ G, 0 < g ∧ g ≤ B)
    (hSG : ∀ ℓ ∈ S, ℓ ∉ G → B < ℓ) (hc : S.card ≤ G.card) :
    ∑ ℓ ∈ S, 1 / (ℓ : ℝ) ≤ ∑ ℓ ∈ G, 1 / (ℓ : ℝ) := by
  rw [← Finset.sum_inter_add_sum_sdiff S G, ← Finset.sum_inter_add_sum_sdiff G S,
    Finset.inter_comm G S]
  have hcard : (S \ G).card ≤ (G \ S).card := by
    have h1 := Finset.card_sdiff_add_card_inter S G
    have h2 := Finset.card_sdiff_add_card_inter G S
    rw [Finset.inter_comm G S] at h2
    omega
  have hBpos : 0 < B ∨ G = ∅ := by
    rcases G.eq_empty_or_nonempty with h | ⟨g, hg⟩
    · exact Or.inr h
    · exact Or.inl (lt_of_lt_of_le (hG g hg).1 (hG g hg).2)
  rcases hBpos with hB | hGe
  · have hBR : (0 : ℝ) < B := by exact_mod_cast hB
    have h1 : ∑ ℓ ∈ S \ G, 1 / (ℓ : ℝ) ≤ (S \ G).card • (1 / (B : ℝ)) := by
      refine Finset.sum_le_card_nsmul _ _ _ fun ℓ hℓ => ?_
      obtain ⟨hℓS, hℓG⟩ := Finset.mem_sdiff.mp hℓ
      have := hSG ℓ hℓS hℓG
      have hℓR : (B : ℝ) < ℓ := by exact_mod_cast this
      exact one_div_le_one_div_of_le hBR hℓR.le
    have h2 : (G \ S).card • (1 / (B : ℝ)) ≤ ∑ ℓ ∈ G \ S, 1 / (ℓ : ℝ) := by
      refine Finset.card_nsmul_le_sum _ _ _ fun ℓ hℓ => ?_
      have hg := hG ℓ (Finset.mem_sdiff.mp hℓ).1
      have h0 : (0 : ℝ) < ℓ := by exact_mod_cast hg.1
      exact one_div_le_one_div_of_le h0 (by exact_mod_cast hg.2)
    have h3 : (S \ G).card • (1 / (B : ℝ)) ≤ (G \ S).card • (1 / (B : ℝ)) := by
      rw [nsmul_eq_mul, nsmul_eq_mul]
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) (by positivity)
    linarith
  · subst hGe
    have : S = ∅ := Finset.card_eq_zero.mp (by simpa using hc)
    subst this
    simp

/-- The first primes `≥ 5`, up to `B`. -/
def G (B : ℕ) : Finset ℕ := (Finset.range (B + 1)).filter fun ℓ => ℓ.Prime ∧ 5 ≤ ℓ

lemma two_mem {P : ℕ} (hP : P.Prime) (h3 : 3 ≤ P) : 2 ∈ (P - 1).primeFactors := by
  rw [Nat.mem_primeFactors]
  refine ⟨Nat.prime_two, ?_, by omega⟩
  obtain ⟨k, hk⟩ := hP.odd_of_ne_two (by omega)
  exact ⟨k, by omega⟩

lemma small_eq {P : ℕ} (hP : P.Prime) (h3 : 3 ≤ P) :
    (P - 1).primeFactors.filter (fun ℓ => ¬ 5 ≤ ℓ)
      = if 3 ∈ (P - 1).primeFactors then {2, 3} else {2} := by
  have h2 := two_mem hP h3
  ext ℓ
  simp only [Finset.mem_filter]
  split_ifs with h3F
  · simp only [Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨hm, hl⟩
      have hpr := Nat.prime_of_mem_primeFactors hm
      interval_cases ℓ <;> norm_num at hpr ⊢
    · rintro (rfl | rfl) <;> simp_all
  · simp only [Finset.mem_singleton]
    constructor
    · rintro ⟨hm, hl⟩
      have hpr := Nat.prime_of_mem_primeFactors hm
      interval_cases ℓ <;> norm_num at hpr ⊢
      exact absurd hm h3F
    · rintro rfl; simp_all

/-- `δ_S`, `θ_{F∖S}` and `K` for `S = {ℓ ∈ F : ℓ ≥ 5}`. -/
lemma sieve_data {P : ℕ} (hP : P.Prime) (h3 : 3 ≤ P) (B M e : ℕ) (dM th : ℝ)
    (hGc : (G B).card = M) (hGs : dM ≤ 1 - ∑ ℓ ∈ G B, 1 / (ℓ : ℝ)) (hdM : 0 < dM) (hM : 1 ≤ M)
    (he : ((P - 1).primeFactors.filter (fun ℓ => ¬ 5 ≤ ℓ)).card = e)
    (hth : th ≤ θ ((P - 1).primeFactors.filter (fun ℓ => ¬ 5 ≤ ℓ))) (hth0 : 0 ≤ th)
    (hcard : ((P - 1).primeFactors.filter (fun ℓ => 5 ≤ ℓ)).card ≤ M) :
    let S := (P - 1).primeFactors.filter (fun ℓ => 5 ≤ ℓ)
    0 < deltaOf S ∧ dM * th ≤ deltaOf S * θ ((P - 1).primeFactors \ S) ∧
      sieveK P S ≤ 2 ^ e * (2 + ((M : ℝ) - 1) / dM) - 1 := by
  intro S
  set F := (P - 1).primeFactors with hF
  have hδ : dM ≤ deltaOf S := by
    have := sum_inv_le S (G B) B
      (fun g hg => by
        simp only [G, Finset.mem_filter, Finset.mem_range] at hg
        exact ⟨by omega, by omega⟩)
      (fun ℓ hℓ hℓG => by
        simp only [S, Finset.mem_filter] at hℓ
        simp only [G, Finset.mem_filter, Finset.mem_range, not_and] at hℓG
        by_contra hcon
        exact hℓG (by omega) (Nat.prime_of_mem_primeFactors hℓ.1) hℓ.2)
      (by rw [hGc]; exact hcard)
    unfold deltaOf; linarith
  have hδpos : 0 < deltaOf S := lt_of_lt_of_le hdM hδ
  have hsd : F \ S = F.filter (fun ℓ => ¬ 5 ≤ ℓ) := (Finset.filter_not _ _).symm
  have hθpos : 0 ≤ θ (F \ S) :=
    (Finset.prod_pos fun ℓ hℓ =>
      aR_pos (Nat.prime_of_mem_primeFactors (Finset.sdiff_subset hℓ)).two_le).le
  refine ⟨hδpos, ?_, ?_⟩
  · rw [hsd]
    rw [hsd] at hθpos
    exact mul_le_mul hδ hth hth0 hδpos.le
  · have hcardF : S.card + e = F.card := by
      rw [← he]; exact Finset.card_filter_add_card_filter_not _
    have hexp : F.card - S.card = e := by omega
    unfold sieveK
    rw [hexp]
    have h1 : ((S.card : ℝ) - 1) / deltaOf S ≤ ((M : ℝ) - 1) / deltaOf S :=
      div_le_div_of_nonneg_right (by have : (S.card : ℝ) ≤ M := by exact_mod_cast hcard
                                     linarith) hδpos.le
    have h2 : ((M : ℝ) - 1) / deltaOf S ≤ ((M : ℝ) - 1) / dM :=
      div_le_div_of_nonneg_left (by have : (1 : ℝ) ≤ M := by exact_mod_cast hM
                                    linarith) hdM hδ
    have h2e : (0 : ℝ) ≤ 2 ^ e := by positivity
    have := mul_le_mul_of_nonneg_left (add_le_add_left (h1.trans h2) 2) h2e
    linarith

lemma theta_23 : θ ({2, 3} : Finset ℕ) = 1 / 3 := by
  simp [θ, aR]

lemma theta_2 : θ ({2} : Finset ℕ) = 1 / 2 := by
  simp [θ, aR]

/-- `B · ∏_{r < B prime} r ≤ n` once `ω(n) > π(B - 1)`. -/
lemma mul_prod_le (B n k Q : ℕ) (hn : n ≠ 0) (hB : 0 < B) (hk : k ≤ n.primeFactors.card)
    (hQ : ∏ r ∈ (Finset.range B).filter Nat.Prime, r = Q)
    (hc : ((Finset.range B).filter Nat.Prime).card + 1 = k) : B * Q ≤ n := by
  have h := Erdos985.pow_card_primeFactors_mul_le B n hn
  rw [hQ] at h
  set c := ((Finset.range B).filter Nat.Prime).card
  have hpow : B ^ k ≤ B ^ n.primeFactors.card := Nat.pow_le_pow_right hB hk
  have h2 : B * Q * B ^ c ≤ n * B ^ c := by
    calc B * Q * B ^ c = B ^ k * Q := by rw [← hc, pow_succ]; ring
      _ ≤ B ^ n.primeFactors.card * Q := Nat.mul_le_mul_right _ hpow
      _ ≤ n * B ^ c := h
  exact Nat.le_of_mul_le_mul_right h2 (by positivity)

/-- The constant `∏_{p < 23} 16 p³ / (p - 1)⁴`. -/
noncomputable def smallC : ℝ :=
  ∏ p ∈ ({2, 3, 5, 7, 11, 13, 17, 19} : Finset ℕ), (16 * (p : ℝ) ^ 3 / ((p : ℝ) - 1) ^ 4)

lemma smallC_le : smallC ≤ 517576 := by
  norm_num [smallC, Finset.prod_insert]

/-- `(2^ω / θ_F)^4 ≤ C n` with `F` the prime factors of `n`. -/
lemma D_pow4_le (n : ℕ) (hn : n ≠ 0) :
    ((2 : ℝ) ^ n.primeFactors.card / θ n.primeFactors) ^ 4 ≤ smallC * n := by
  set F := n.primeFactors with hF
  have hF2 : ∀ ℓ ∈ F, 2 ≤ ℓ := fun ℓ h => (Nat.prime_of_mem_primeFactors h).two_le
  set r : ℕ → ℝ := fun ℓ => 16 * (ℓ : ℝ) ^ 3 / ((ℓ : ℝ) - 1) ^ 4 with hr
  have e1 : ((2 : ℝ) ^ F.card / θ F) ^ 4 = (∏ ℓ ∈ F, (ℓ : ℝ)) * ∏ ℓ ∈ F, r ℓ := by
    rw [θ, ← Finset.prod_const, ← Finset.prod_div_distrib, ← Finset.prod_pow,
      ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun ℓ hℓ => ?_
    have h2 : (2 : ℝ) ≤ ℓ := by exact_mod_cast hF2 ℓ hℓ
    have h1 : (ℓ : ℝ) - 1 ≠ 0 := by linarith
    have h0 : (ℓ : ℝ) ≠ 0 := by linarith
    simp only [aR, hr]
    field_simp
    ring
  rw [e1]
  have hprod : (∏ ℓ ∈ F, (ℓ : ℝ)) ≤ n := by
    have := Nat.le_of_dvd (Nat.pos_of_ne_zero hn) (Nat.prod_primeFactors_dvd n)
    have h' : ((∏ p ∈ F, p : ℕ) : ℝ) ≤ n := by exact_mod_cast this
    simpa [Nat.cast_prod] using h'
  have hr0 : ∀ ℓ ∈ F, 0 ≤ r ℓ := fun ℓ hℓ => by
    have h2 : (2 : ℝ) ≤ ℓ := by exact_mod_cast hF2 ℓ hℓ
    simp only [hr]
    have : (0 : ℝ) ≤ (ℓ : ℝ) - 1 := by linarith
    positivity
  have hrF : ∏ ℓ ∈ F, r ℓ ≤ smallC := by
    rw [← Finset.prod_filter_mul_prod_filter_not F (fun ℓ => ℓ < 23)]
    have hbig : ∏ ℓ ∈ F.filter (fun ℓ => ¬ ℓ < 23), r ℓ ≤ 1 := by
      refine Finset.prod_le_one₀ (fun ℓ hℓ => hr0 ℓ (Finset.filter_subset _ _ hℓ)) fun ℓ hℓ => ?_
      have h23 : (23 : ℝ) ≤ ℓ := by
        have := (Finset.mem_filter.mp hℓ).2
        exact_mod_cast (by omega : 23 ≤ ℓ)
      simp only [hr]
      have hl1 : (0 : ℝ) < (ℓ : ℝ) - 1 := by linarith
      rw [div_le_one (by positivity)]
      set t := (ℓ : ℝ) - 1 with ht
      have ht22 : 22 ≤ t := by linarith
      have e : (ℓ : ℝ) = t + 1 := by linarith
      rw [e]
      nlinarith [mul_nonneg (mul_nonneg (sub_nonneg.2 ht22) (sub_nonneg.2 ht22))
        (sub_nonneg.2 ht22), mul_nonneg (sub_nonneg.2 ht22) (sub_nonneg.2 ht22),
        sq_nonneg t, mul_nonneg (sq_nonneg t) (sub_nonneg.2 ht22)]
    set small : Finset ℕ := {2, 3, 5, 7, 11, 13, 17, 19}
    have hsub : F.filter (fun ℓ => ℓ < 23) ⊆ small := by
      intro ℓ hℓ
      obtain ⟨hm, hl⟩ := Finset.mem_filter.mp hℓ
      have hpr := Nat.prime_of_mem_primeFactors hm
      have : ∀ m < 23, m.Prime → m ∈ small := by decide
      exact this ℓ hl hpr
    have hone : ∀ ℓ ∈ small, 1 ≤ r ℓ := by
      intro ℓ hℓ
      simp only [small, Finset.mem_insert, Finset.mem_singleton] at hℓ
      simp only [hr]
      rcases hℓ with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num
    have hsmall : ∏ ℓ ∈ F.filter (fun ℓ => ℓ < 23), r ℓ ≤ smallC := by
      have hC : smallC = ∏ ℓ ∈ small, r ℓ := rfl
      rw [hC, ← Finset.prod_sdiff hsub]
      have h1 : 1 ≤ ∏ ℓ ∈ small \ F.filter (fun ℓ => ℓ < 23), r ℓ := by
        have := Finset.prod_le_prod₀ (s := small \ F.filter (fun ℓ => ℓ < 23)) (f := fun _ => (1 : ℝ))
          (g := r) (fun _ _ => zero_le_one) (fun ℓ hℓ => hone ℓ (Finset.sdiff_subset hℓ))
        simpa using this
      have h0 : 0 ≤ ∏ ℓ ∈ F.filter (fun ℓ => ℓ < 23), r ℓ :=
        Finset.prod_nonneg fun ℓ hℓ => hr0 ℓ (Finset.filter_subset _ _ hℓ)
      nlinarith
    have h0b : 0 ≤ ∏ ℓ ∈ F.filter (fun ℓ => ¬ ℓ < 23), r ℓ :=
      Finset.prod_nonneg fun ℓ hℓ => hr0 ℓ (Finset.filter_subset _ _ hℓ)
    have h0s : 0 ≤ ∏ ℓ ∈ F.filter (fun ℓ => ℓ < 23), r ℓ :=
      Finset.prod_nonneg fun ℓ hℓ => hr0 ℓ (Finset.filter_subset _ _ hℓ)
    calc (∏ ℓ ∈ F.filter (fun ℓ => ℓ < 23), r ℓ) * ∏ ℓ ∈ F.filter (fun ℓ => ¬ ℓ < 23), r ℓ
        ≤ smallC * 1 := mul_le_mul hsmall hbig h0b (h0s.trans hsmall)
      _ = smallC := mul_one _
  have hC0 : 0 ≤ smallC := le_trans (Finset.prod_nonneg hr0) hrF
  calc (∏ ℓ ∈ F, (ℓ : ℝ)) * ∏ ℓ ∈ F, r ℓ ≤ n * smallC :=
        mul_le_mul hprod hrF (Finset.prod_nonneg hr0) (Nat.cast_nonneg _)
    _ = smallC * n := mul_comm _ _

/-! ## The sums `Σ 1/ℓ` over the first primes `≥ 5` -/

lemma G19 : (G 19).card = 6 ∧ (0.377855 : ℝ) ≤ 1 - ∑ ℓ ∈ G 19, 1 / (ℓ : ℝ) := by
  rw [show G 19 = {5, 7, 11, 13, 17, 19} by decide]
  refine ⟨by decide, ?_⟩
  norm_num [Finset.sum_insert]

lemma G23 : (G 23).card = 7 ∧ (0.334377 : ℝ) ≤ 1 - ∑ ℓ ∈ G 23, 1 / (ℓ : ℝ) := by
  rw [show G 23 = {5, 7, 11, 13, 17, 19, 23} by decide]
  refine ⟨by decide, ?_⟩
  norm_num [Finset.sum_insert]

lemma G29 : (G 29).card = 8 ∧ (0.299894 : ℝ) ≤ 1 - ∑ ℓ ∈ G 29, 1 / (ℓ : ℝ) := by
  rw [show G 29 = {5, 7, 11, 13, 17, 19, 23, 29} by decide]
  refine ⟨by decide, ?_⟩
  norm_num [Finset.sum_insert]

lemma G43 : (G 43).card = 12 ∧ (0.192963 : ℝ) ≤ 1 - ∑ ℓ ∈ G 43, 1 / (ℓ : ℝ) := by
  rw [show G 43 = {5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43} by decide]
  refine ⟨by decide, ?_⟩
  norm_num [Finset.sum_insert]

lemma G47 : (G 47).card = 13 ∧ (0.171686 : ℝ) ≤ 1 - ∑ ℓ ∈ G 47, 1 / (ℓ : ℝ) := by
  rw [show G 47 = {5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47} by decide]
  refine ⟨by decide, ?_⟩
  norm_num [Finset.sum_insert]

/-! ## The seven cases -/

/-- The sieve cases share this shape: given the bounds `dt0 ≤ δθ`, `K ≤ K0` on the sieve
constants, `SieveIneq` holds. -/
theorem sieveNumerics_10_8 : SieveNumerics 100000000 := by
  intro P hP hP8
  have h3 : 3 ≤ P := by omega
  have hn : P - 1 ≠ 0 := by omega
  set F := (P - 1).primeFactors with hF
  set S := F.filter (fun ℓ => 5 ≤ ℓ) with hS
  have hSF : S ⊆ F := Finset.filter_subset _ _
  have hcardFS : S.card + (F.filter (fun ℓ => ¬ 5 ≤ ℓ)).card = F.card :=
    Finset.card_filter_add_card_filter_not _
  have hE := small_eq hP h3
  by_cases hω : 15 ≤ F.card
  · -- no sieve
    refine ⟨∅, Finset.empty_subset _, by simp [deltaOf], ?_⟩
    have hPlow : 614889782588491411 ≤ P := by
      have := mul_prod_le 47 (P - 1) 15 13082761331670030 hn (by norm_num) hω (by decide)
        (by decide)
      omega
    have hD : ((2 : ℝ) ^ F.card / θ F) ^ 4 ≤ 517576 * P := by
      have h1 := D_pow4_le (P - 1) hn
      have h2 : ((P - 1 : ℕ) : ℝ) ≤ P := by exact_mod_cast Nat.sub_le P 1
      have h0 : (0 : ℝ) ≤ ((P - 1 : ℕ) : ℝ) := Nat.cast_nonneg _
      calc ((2 : ℝ) ^ F.card / θ F) ^ 4 ≤ smallC * ((P - 1 : ℕ) : ℝ) := h1
        _ ≤ 517576 * P := mul_le_mul smallC_le h2 h0 (by norm_num)
    exact sieveIneq_empty_of 614889782588491411
      (60 * 0.6931471808 + 614889782588491411 / 2 ^ 60 - 1) 101806004 466 517576 (999 / 400)
      (671 / 1000) 0.499999 (by norm_num) (log_le_U _ _ (by norm_num)) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hPlow hD
  · -- sieve with `S = {ℓ ∈ F : ℓ ≥ 5}`
    refine ⟨S, hSF, ?_⟩
    have hdata := fun B M e dM th hGc hGs hdM hM he hth hth0 hcard =>
      sieve_data hP h3 B M e dM th hGc hGs hdM hM he hth hth0 hcard
    by_cases h3F : 3 ∈ F
    · -- `E = {2, 3}`
      have hEe : F.filter (fun ℓ => ¬ 5 ≤ ℓ) = {2, 3} := by rw [hE, if_pos h3F]
      have he : (F.filter (fun ℓ => ¬ 5 ≤ ℓ)).card = 2 := by rw [hEe]; decide
      have hth : (1 / 3 : ℝ) ≤ θ (F.filter (fun ℓ => ¬ 5 ≤ ℓ)) := by rw [hEe, theta_23]
      rcases (show F.card ≤ 8 ∨ F.card = 9 ∨ 10 ≤ F.card by omega) with h8 | h9 | h10
      · obtain ⟨hδ, hdt, hK⟩ := hdata 19 6 2 0.377855 (1 / 3) G19.1 G19.2 (by norm_num)
          (by norm_num) he hth (by norm_num) (by omega)
        refine ⟨hδ, sieveIneq_of 100000000 (27 * 0.6931471808 + 100000000 / 2 ^ 27 - 1) 1937 12
          0.125951 59.931 77.779 41.35 (by norm_num) (log_le_U _ _ (by norm_num)) (by norm_num)
          (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
          (by norm_num) (by norm_num) (by norm_num) (by norm_num) hP8 S
          (le_trans (by norm_num) hdt) (hK.trans (by norm_num))⟩
      · have hPlow : 223092871 ≤ P := by
          have := mul_prod_le 23 (P - 1) 9 9699690 hn (by norm_num) (by omega) (by decide)
            (by decide)
          omega
        obtain ⟨hδ, hdt, hK⟩ := hdata 23 7 2 0.334377 (1 / 3) G23.1 G23.2 (by norm_num)
          (by norm_num) he hth (by norm_num) (by omega)
        refine ⟨hδ, sieveIneq_of 223092871 (28 * 0.6931471808 + 223092871 / 2 ^ 28 - 1) 2835 14
          0.111459 78.776 100.135 53.864 (by norm_num) (log_le_U _ _ (by norm_num)) (by norm_num)
          (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
          (by norm_num) (by norm_num) (by norm_num) (by norm_num) hPlow S
          (le_trans (by norm_num) hdt) (hK.trans (by norm_num))⟩
      · have hPlow : 6469693231 ≤ P := by
          have := mul_prod_le 29 (P - 1) 10 223092870 hn (by norm_num) h10 (by decide)
            (by decide)
          omega
        obtain ⟨hδ, hdt, hK⟩ := hdata 43 12 2 0.192963 (1 / 3) G43.1 G43.2 (by norm_num)
          (by norm_num) he hth (by norm_num) (by omega)
        refine ⟨hδ, sieveIneq_of 6469693231 (33 * 0.6931471808 + 6469693231 / 2 ^ 33 - 1) 14077 24
          0.064321 235.023 282.811 158.017 (by norm_num) (log_le_U _ _ (by norm_num))
          (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
          (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hPlow S
          (le_trans (by norm_num) hdt) (hK.trans (by norm_num))⟩
    · -- `E = {2}`
      have hEe : F.filter (fun ℓ => ¬ 5 ≤ ℓ) = {2} := by rw [hE, if_neg h3F]
      have he : (F.filter (fun ℓ => ¬ 5 ≤ ℓ)).card = 1 := by rw [hEe]; decide
      have hth : (1 / 2 : ℝ) ≤ θ (F.filter (fun ℓ => ¬ 5 ≤ ℓ)) := by rw [hEe, theta_2]
      rcases (show F.card ≤ 8 ∨ F.card = 9 ∨ 10 ≤ F.card by omega) with h8 | h9 | h10
      · obtain ⟨hδ, hdt, hK⟩ := hdata 23 7 1 0.334377 (1 / 2) G23.1 G23.2 (by norm_num)
          (by norm_num) he hth (by norm_num) (by omega)
        refine ⟨hδ, sieveIneq_of 100000000 (27 * 0.6931471808 + 100000000 / 2 ^ 27 - 1) 1937 12
          0.167188 38.888 51.638 26.97 (by norm_num) (log_le_U _ _ (by norm_num)) (by norm_num)
          (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
          (by norm_num) (by norm_num) (by norm_num) (by norm_num) hP8 S
          (le_trans (by norm_num) hdt) (hK.trans (by norm_num))⟩
      · have hPlow : 223092871 ≤ P := by
          have := mul_prod_le 23 (P - 1) 9 9699690 hn (by norm_num) (by omega) (by decide)
            (by decide)
          omega
        obtain ⟨hδ, hdt, hK⟩ := hdata 29 8 1 0.299894 (1 / 2) G29.1 G29.2 (by norm_num)
          (by norm_num) he hth (by norm_num) (by omega)
        refine ⟨hδ, sieveIneq_of 223092871 (28 * 0.6931471808 + 223092871 / 2 ^ 28 - 1) 2835 14
          0.149947 49.684 64.575 34.117 (by norm_num) (log_le_U _ _ (by norm_num)) (by norm_num)
          (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
          (by norm_num) (by norm_num) (by norm_num) (by norm_num) hPlow S
          (le_trans (by norm_num) hdt) (hK.trans (by norm_num))⟩
      · have hPlow : 6469693231 ≤ P := by
          have := mul_prod_le 29 (P - 1) 10 223092870 hn (by norm_num) h10 (by decide)
            (by decide)
          omega
        obtain ⟨hδ, hdt, hK⟩ := hdata 47 13 1 0.171686 (1 / 2) G47.1 G47.2 (by norm_num)
          (by norm_num) he hth (by norm_num) (by omega)
        refine ⟨hδ, sieveIneq_of 6469693231 (33 * 0.6931471808 + 6469693231 / 2 ^ 33 - 1) 14077 24
          0.085843 142.791 174.899 96.189 (by norm_num) (log_le_U _ _ (by norm_num))
          (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
          (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hPlow S
          (le_trans (by norm_num) hdt) (hK.trans (by norm_num))⟩

end SunA243164.Numerics
