import SunPrimeDensity.Statement
import SunPrimeDensity.Tail
import SunPrimeDensity.Check
import SunPrimeDensity.Tail3

/-!
# Sun's conjecture for every exponent `k ≥ 4`, from RH

* `n^k ≥ 10¹⁰`: `tail`, from Schoenfeld's bound `|π(x) − li(x)| < √x log x/(8π)` (`x ≥ 2657`);
* `n^k < 10¹⁰`: `Check.finite_range`, 565 pairs, checked exactly (83 pairs, primes counted up
  to `41⁴`) or analytically with Schoenfeld's bound and the PsiCert bound on `[4·10⁵, 10¹⁰]`.

Schoenfeld's bound is schoenfeld-rh's `schoenfeldPi_of_RH`, so RH is the only hypothesis.
-/

namespace SunPrimeDensity

open Schoenfeld

/-- The real form of the inequality, from Schoenfeld's bound. -/
theorem ratio_lt_of_schoenfeld (hS : SchoenfeldPi) {k n : ℕ} (hk : 4 ≤ k) (hn : 2 ≤ n) :
    (Nat.primeCounting ((n + 1) ^ k) : ℝ) / (((n : ℝ) + 1) ^ k) <
      (Nat.primeCounting (n ^ k) : ℝ) / ((n : ℝ) ^ k) := by
  rcases lt_or_ge (n ^ k) (10 ^ 10) with h | h
  · exact Check.finite_range hS hk hn h
  · have := tail hS hk hn h
    push_cast at this
    exact this

/-- **Sun's conjecture for `k ≥ 4`, from Schoenfeld's bound** (`SchoenfeldPi`). -/
theorem sunConjectureFrom_four_of_schoenfeld (hS : SchoenfeldPi) : SunConjectureFrom 4 := by
  intro k hk n hn
  rw [← Rat.cast_lt (K := ℝ)]
  push_cast
  exact ratio_lt_of_schoenfeld hS hk hn

/-- **Sun's conjecture (OEIS A038098) for every exponent `k ≥ 4`, from RH**:
`π((n+1)^k)/(n+1)^k < π(n^k)/n^k` for all `k ≥ 4` and `n ≥ 2`. -/
theorem sun_of_RH (hRH : RiemannHypothesis) (k : ℕ) (hk : 4 ≤ k) (n : ℕ) (hn : 2 ≤ n) :
    (Nat.primeCounting ((n + 1) ^ k) : ℚ) / ((n + 1) ^ k : ℚ) <
    (Nat.primeCounting (n ^ k) : ℚ) / (n ^ k : ℚ) :=
  sunConjectureFrom_four_of_schoenfeld (schoenfeldPi_of_RH hRH) k hk n hn

/-- `SunConjectureFrom 4` from RH. -/
theorem sunConjectureFrom_four_of_RH (hRH : RiemannHypothesis) : SunConjectureFrom 4 :=
  sunConjectureFrom_four_of_schoenfeld (schoenfeldPi_of_RH hRH)

/-- Sun's conjecture reduces, under RH, to the single exponent `k = 3`. -/
theorem sunConjecture_of_RH_of_three (hRH : RiemannHypothesis)
    (h3 : ∀ n : ℕ, 2 ≤ n →
      (Nat.primeCounting ((n + 1) ^ 3) : ℚ) / ((n + 1) ^ 3 : ℚ) <
      (Nat.primeCounting (n ^ 3) : ℚ) / (n ^ 3 : ℚ)) : SunConjecture := by
  intro k hk n hn
  rcases Nat.lt_or_ge k 4 with h | h
  · obtain rfl : k = 3 := by omega
    exact h3 n hn
  · exact sun_of_RH hRH k h n hn

/-- **`k = 3` outside `141 ≤ n < 10⁷`, from RH**: for `2 ≤ n ≤ 140` by exact prime counts, and
for `n ≥ 10⁷` from Schoenfeld's bound. -/
theorem sun_three_of_RH (hRH : RiemannHypothesis) (n : ℕ) (hn : 2 ≤ n)
    (hrange : n ≤ 140 ∨ 10 ^ 7 ≤ n) :
    (Nat.primeCounting ((n + 1) ^ 3) : ℚ) / ((n + 1) ^ 3 : ℚ) <
    (Nat.primeCounting (n ^ 3) : ℚ) / (n ^ 3 : ℚ) := by
  rw [← Rat.cast_lt (K := ℝ)]
  push_cast
  rcases hrange with h | h
  · exact Check.three_small hn h
  · exact tail_three (schoenfeldPi_of_RH hRH) h

/-- Under RH, Sun's conjecture (all `k > 2`) is equivalent to its case `k = 3`,
`141 ≤ n < 10⁷`. -/
theorem sunConjecture_iff_of_RH (hRH : RiemannHypothesis) :
    SunConjecture ↔ ∀ n : ℕ, 141 ≤ n → n < 10 ^ 7 →
      (Nat.primeCounting ((n + 1) ^ 3) : ℚ) / ((n + 1) ^ 3 : ℚ) <
      (Nat.primeCounting (n ^ 3) : ℚ) / (n ^ 3 : ℚ) := by
  constructor
  · intro h n hn _
    exact h 3 (by norm_num) n (by omega)
  · intro h3
    refine sunConjecture_of_RH_of_three hRH fun n hn => ?_
    rcases Nat.lt_or_ge n 141 with h1 | h1
    · exact sun_three_of_RH hRH n hn (Or.inl (by omega))
    rcases Nat.lt_or_ge n (10 ^ 7) with h2 | h2
    · exact h3 n h1 h2
    · exact sun_three_of_RH hRH n hn (Or.inr h2)

end SunPrimeDensity
