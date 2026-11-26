import Implications.PrimeGaps.FiroozbakhtOppermann
import Implications.PrimeGaps.Granville.Statement

/-!
# Firoozbakht's conjecture: explicit and asymptotic gap bounds (towards Kourbatov's bound)

formal-conjectures states (`Firoozbakht.firoozbakht_conjecture_consequence`, copied verbatim as
`Firoozbakht.FiroozbakhtConsequence` in `Implications.PrimeGaps.Granville.Statement`) that
Firoozbakht's conjecture gives `p_{n+1} - p_n < (log p_n)² - log p_n` for `n ≥ 4` (Kourbatov
2015, unverified). **That sharp form is not proved here.** What is proved, from
`Firoozbakht.FiroozbakhtConjecture` alone:

* `gap_lt_of_firoozbakht_explicit`: `p_{n+1} - p_n < (log p_n)² / log 2 + (log 2)²` once
  `p_n ≥ 2^16` (Chebyshev's `π(x) log x ≥ x log 2`, `Chebyshev.psi_ge_of_seven_le`);
  `1 / log 2 ≈ 1.4427`.
* `gap_lt_of_firoozbakht_eventually`: for every `ε > 0`, `p_{n+1} - p_n < (1 + ε) (log p_n)²`
  for all large `n` (Mathlib's prime number theorem `Nat.isEquivalent_primeCounting`).

**Why the sharp form is out of reach.** Firoozbakht at `n` says exactly
`p_{n+1} < p_n exp(t)` with `t = log p_n / (n + 1) = log p_n / π(p_n)`, so the gap is at most
`p_n (e^t - 1) ≈ (log p_n) · p_n / π(p_n)`. With `L = log p_n`, Kourbatov's `L² - L` needs
`p_n / π(p_n) < L - 1 - O(L²/p_n)`, i.e. `π(x) > x / (log x - 1)` with an explicit threshold
(Dusart: for `x ≥ 5393`). Since `x / (log x - 1) = x/L + x/L² + x/L³ + …` while
`π(x) = x/L + x/L² + 2x/L³ + …`, this needs the prime number theorem with an explicit error term
`O(x / log³ x)`; Mathlib has only the asymptotic PNT (no rate) and Chebyshev's constant `log 2`.
In numbers: the target bound is `L² - L`; Chebyshev gives `1.4427 L²` and PNT gives
`(1 + ε) L²`, so the remaining gap is a factor `1 + ε` plus the linear term `L`.
-/

open Filter Real

namespace Implications.PrimeGaps

/-- **Firoozbakht, unrolled.** With `a = p_k`, `t = log a / (k + 1)` and `t ≤ 1`, Firoozbakht's
conjecture gives `p_{k+1} - p_k < a t + a t²`. -/
theorem gap_lt_of_firoozbakht_core (h : Firoozbakht.FiroozbakhtConjecture) (k : ℕ)
    (ht1 : Real.log (Nat.nth Nat.Prime k) / (k + 1) ≤ 1) :
    (primeGap k : ℝ) < (Nat.nth Nat.Prime k : ℝ) * (Real.log (Nat.nth Nat.Prime k) / (k + 1)) +
      (Nat.nth Nat.Prime k : ℝ) * (Real.log (Nat.nth Nat.Prime k) / (k + 1)) ^ 2 := by
  have hPrime : (fun n : ℕ => Prime n) = Nat.Prime :=
    funext fun n ↦ propext _root_.Nat.prime_iff.symm
  set a : ℝ := (Nat.nth Nat.Prime k : ℝ) with ha
  set b : ℝ := (Nat.nth Nat.Prime (k + 1) : ℝ) with hb
  have ha2 : (2 : ℝ) ≤ a := by rw [ha]; exact_mod_cast (_root_.Nat.prime_nth_prime k).two_le
  have ha0 : 0 < a := by linarith
  have hb0 : 0 < b := by
    have := (_root_.Nat.prime_nth_prime (k + 1)).pos
    rw [hb]; exact_mod_cast this
  have hla : 0 < Real.log a := Real.log_pos (by linarith)
  have hF := h k
  simp only [Firoozbakht.firoozbakhtSeq, hPrime] at hF
  rw [← ha, ← hb] at hF
  have hF' := Real.log_lt_log (Real.rpow_pos_of_pos hb0 _) hF
  rw [Real.log_rpow hb0, Real.log_rpow ha0] at hF'
  push_cast at hF'
  set L := Real.log a with hL
  set t : ℝ := L / (k + 1 : ℝ) with ht
  have hlogb : Real.log b < L + t := by
    have e1 : Real.log b = (k + 1 + 1) * (1 / ((k : ℝ) + 1 + 1) * Real.log b) := by
      field_simp
    have e2 : L + t = (k + 1 + 1) * (1 / ((k : ℝ) + 1) * L) := by
      rw [ht]; field_simp
    rw [e1, e2]
    exact mul_lt_mul_of_pos_left hF' (by positivity)
  have hbexp : b < a * Real.exp t := by
    have := Real.exp_lt_exp.2 hlogb
    rwa [Real.exp_log hb0, Real.exp_add, hL, Real.exp_log ha0] at this
  have ht0 : 0 ≤ t := by positivity
  have hexp : Real.exp t ≤ 1 + t + t ^ 2 := by
    have := Real.abs_exp_sub_one_sub_id_le (x := t) (by rw [abs_of_nonneg ht0]; exact ht1)
    have := (le_abs_self _).trans this
    linarith
  have hgap : (primeGap k : ℝ) = b - a := by
    rw [primeGap, Nat.cast_sub (nth_lt_nth_succ k).le, hb, ha]
  rw [hgap]
  nlinarith

/-- **Explicit gap bound from Firoozbakht's conjecture**:
`p_{k+1} - p_k < (log p_k)² / log 2 + (log 2)²` once `p_k ≥ 2^16`. -/
theorem gap_lt_of_firoozbakht_explicit (h : Firoozbakht.FiroozbakhtConjecture) {k : ℕ}
    (hk : 65536 ≤ Nat.nth Nat.Prime k) :
    (primeGap k : ℝ) < Real.log (Nat.nth Nat.Prime k) ^ 2 / Real.log 2 + Real.log 2 ^ 2 := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hlog2' := Real.log_two_lt_d9
  set a : ℝ := (Nat.nth Nat.Prime k : ℝ) with ha
  have ha16 : (65536 : ℝ) ≤ a := by rw [ha]; exact_mod_cast hk
  have ha0 : 0 < a := by linarith
  set L := Real.log a with hL
  have hla : 0 < L := Real.log_pos (by linarith)
  set t : ℝ := L / (k + 1 : ℝ) with ht
  have hk1 : (0 : ℝ) < k + 1 := by positivity
  have ht0 : 0 ≤ t := by positivity
  -- Chebyshev: `a log 2 ≤ (k + 1) L`, so `a t log 2 ≤ L²`
  have hcheb := nth_mul_log_two_le (k := k) (by omega)
  rw [← ha, ← hL] at hcheb
  have htk : t * (k + 1) = L := by rw [ht]; field_simp
  have hat : a * t * Real.log 2 ≤ L ^ 2 := by
    have h1 : (k + 1 : ℝ) * (a * t * Real.log 2) ≤ (k + 1) * L ^ 2 := by
      have : (k + 1 : ℝ) * (a * t * Real.log 2) = (a * Real.log 2) * (t * (k + 1)) := by ring
      rw [this, htk]
      have := mul_le_mul_of_nonneg_right hcheb hla.le
      nlinarith
    exact le_of_mul_le_mul_left h1 hk1
  -- `L² ≤ (log 2)² √a`
  have hL2 : L ^ 2 ≤ Real.log 2 ^ 2 * Real.sqrt a := log_sq_le_of_ge ha16
  set s := Real.sqrt a with hs
  have hss : s ^ 2 = a := Real.sq_sqrt ha0.le
  have hs256 : (256 : ℝ) ≤ s := by
    have : Real.sqrt 65536 = 256 := by
      rw [show (65536 : ℝ) = 256 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
    rw [← this, hs]; exact Real.sqrt_le_sqrt ha16
  have hat' : a * t ≤ Real.log 2 * s := by
    have : a * t * Real.log 2 ≤ (Real.log 2 * s) * Real.log 2 := by nlinarith
    exact le_of_mul_le_mul_right this hlog2
  have hts : t * s ≤ Real.log 2 := by
    rw [← hss] at hat'
    have : s * (t * s) ≤ s * Real.log 2 := by nlinarith
    exact le_of_mul_le_mul_left this (by linarith)
  have ht1 : t ≤ 1 := by nlinarith
  have hcore := gap_lt_of_firoozbakht_core h k ht1
  rw [← ha, ← hL, ← ht] at hcore
  have h1 : a * t ≤ L ^ 2 / Real.log 2 := by rw [le_div_iff₀ hlog2]; exact hat
  have h2 : a * t ^ 2 ≤ Real.log 2 ^ 2 := by
    have e : a * t ^ 2 = (a * t) * t := by ring
    rw [e]
    have := mul_le_mul_of_nonneg_right hat' ht0
    have := mul_le_mul_of_nonneg_left hts hlog2.le
    nlinarith
  linarith

/-- **Asymptotic gap bound from Firoozbakht's conjecture**: for every `ε > 0`,
`p_{k+1} - p_k < (1 + ε) (log p_k)²` for all large `k`. -/
theorem gap_lt_of_firoozbakht_eventually (h : Firoozbakht.FiroozbakhtConjecture) {ε : ℝ}
    (hε : 0 < ε) :
    ∀ᶠ k : ℕ in atTop, (primeGap k : ℝ) < (1 + ε) * Real.log (Nat.nth Nat.Prime k) ^ 2 := by
  set δ : ℝ := min (1 / 2) (ε / 4) with hδ
  have hδ0 : 0 < δ := by positivity
  have hδ1 : δ ≤ 1 / 2 := min_le_left _ _
  have hδε : δ ≤ ε / 4 := min_le_right _ _
  -- PNT: `π(x) ≥ (1 - δ) x / log x` for large `x`
  have hpnt := (Nat.isEquivalent_primeCounting.isLittleO.bound hδ0).filter_mono le_rfl
  have hpnt' := tendsto_nth_prime_real.eventually hpnt
  -- `(log x)² ≤ (δ / 2) x` for large `x`
  have hlo : (fun x : ℝ => Real.log x ^ 2) =o[atTop] fun x => x := by
    simpa using isLittleO_log_rpow_rpow_atTop (2 : ℝ) one_pos
  have hsmall := tendsto_nth_prime_real.eventually (hlo.bound (by positivity : 0 < δ / 2))
  have hbig := tendsto_nth_prime_real.eventually (eventually_ge_atTop (3 : ℝ))
  filter_upwards [hpnt', hsmall, hbig] with k hk hks hk3
  set a : ℝ := (Nat.nth Nat.Prime k : ℝ) with ha
  have ha0 : 0 < a := by linarith
  set L := Real.log a with hL
  have hla : 0 < L := Real.log_pos (by linarith)
  have hfloor : ⌊a⌋₊ = Nat.nth Nat.Prime k := by rw [ha, Nat.floor_natCast]
  simp only [hfloor, primeCounting_nth, Real.norm_eq_abs] at hk
  push_cast at hk
  rw [abs_of_pos (by positivity : 0 < a / L)] at hk
  have hπ : (1 - δ) * (a / L) ≤ (k + 1 : ℝ) := by
    have := (neg_abs_le _).trans (le_of_eq rfl) |>.trans' (neg_le_neg hk)
    linarith [neg_abs_le ((k + 1 : ℝ) - a / L)]
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _),
    abs_of_pos ha0] at hks
  set t : ℝ := L / (k + 1 : ℝ) with ht
  have hk1 : (0 : ℝ) < k + 1 := by positivity
  have ht0 : 0 ≤ t := by positivity
  -- `a t ≤ L² / (1 - δ)`
  have hat : a * t * (1 - δ) ≤ L ^ 2 := by
    have htk : t * (k + 1) = L := by rw [ht]; field_simp
    have h1 : (k + 1 : ℝ) * (a * t * (1 - δ)) ≤ (k + 1) * L ^ 2 := by
      have e : (k + 1 : ℝ) * (a * t * (1 - δ)) = a * ((1 - δ) * (t * (k + 1))) := by ring
      rw [e, htk]
      have : (1 - δ) * (a / L) * L ≤ (k + 1) * L := mul_le_mul_of_nonneg_right hπ hla.le
      rw [div_mul_eq_mul_div, mul_div_assoc, div_mul_cancel₀ _ hla.ne'] at this
      nlinarith
    exact le_of_mul_le_mul_left h1 hk1
  -- `t ≤ δ`
  have htδ : t ≤ δ := by
    have h1 : a * t ≤ 2 * L ^ 2 := by nlinarith
    have h2 : a * t ≤ a * δ := by nlinarith
    exact le_of_mul_le_mul_left h2 ha0
  have hcore := gap_lt_of_firoozbakht_core h k (by linarith)
  rw [← ha, ← hL, ← ht] at hcore
  -- `a t (1 + t) ≤ L² (1 + δ) / (1 - δ) ≤ (1 + 4δ) L² ≤ (1 + ε) L²`
  have hL0 : 0 ≤ L ^ 2 := sq_nonneg _
  have hat0 : 0 ≤ a * t := by positivity
  have e : a * t + a * t ^ 2 = a * t * (1 + t) := by ring
  rw [e] at hcore
  have h3 : a * t * (1 + t) * (1 - δ) ≤ L ^ 2 * (1 + δ) := by
    have : a * t * (1 + t) * (1 - δ) = (a * t * (1 - δ)) * (1 + t) := by ring
    rw [this]
    calc (a * t * (1 - δ)) * (1 + t) ≤ L ^ 2 * (1 + t) :=
          mul_le_mul_of_nonneg_right hat (by linarith)
      _ ≤ L ^ 2 * (1 + δ) := mul_le_mul_of_nonneg_left (by linarith) hL0
  have h4 : L ^ 2 * (1 + δ) ≤ (1 + ε) * L ^ 2 * (1 - δ) := by nlinarith
  have h5 : a * t * (1 + t) ≤ (1 + ε) * L ^ 2 :=
    le_of_mul_le_mul_right (h3.trans h4) (by linarith)
  linarith

end Implications.PrimeGaps
