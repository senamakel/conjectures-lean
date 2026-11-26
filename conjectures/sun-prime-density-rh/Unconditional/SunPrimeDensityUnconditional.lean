import Main      -- leanprover-community/riemann-hypothesis: `riemannHypothesis`
import SunPrimeDensity

/-!
# Sun's conjecture for `k ≥ 4`, with RH supplied by the riemann-hypothesis repository

Not part of the default build: it needs the riemann-hypothesis project's compiled modules.
Run `scripts/check-unconditional.sh` to check it.
-/

/-- Sun's conjecture (OEIS A038098) for every exponent `k ≥ 4`. -/
theorem sun_unconditional (k : ℕ) (hk : 4 ≤ k) (n : ℕ) (hn : 2 ≤ n) :
    (Nat.primeCounting ((n + 1) ^ k) : ℚ) / ((n + 1) ^ k : ℚ) <
    (Nat.primeCounting (n ^ k) : ℚ) / (n ^ k : ℚ) :=
  SunPrimeDensity.sun_of_RH riemannHypothesis k hk n hn

theorem sunConjectureFrom_four : SunPrimeDensity.SunConjectureFrom 4 :=
  SunPrimeDensity.sunConjectureFrom_four_of_RH riemannHypothesis

/-- `k = 3` for `2 ≤ n ≤ 140` and for `n ≥ 10⁷`. -/
theorem sun_three_unconditional (n : ℕ) (hn : 2 ≤ n) (hrange : n ≤ 140 ∨ 10 ^ 7 ≤ n) :
    (Nat.primeCounting ((n + 1) ^ 3) : ℚ) / ((n + 1) ^ 3 : ℚ) <
    (Nat.primeCounting (n ^ 3) : ℚ) / (n ^ 3 : ℚ) :=
  SunPrimeDensity.sun_three_of_RH riemannHypothesis n hn hrange

/-- Sun's conjecture is equivalent to its case `k = 3`, `141 ≤ n < 10⁷`. -/
theorem sunConjecture_iff_three_range :
    SunPrimeDensity.SunConjecture ↔ ∀ n : ℕ, 141 ≤ n → n < 10 ^ 7 →
      (Nat.primeCounting ((n + 1) ^ 3) : ℚ) / ((n + 1) ^ 3 : ℚ) <
      (Nat.primeCounting (n ^ 3) : ℚ) / (n ^ 3 : ℚ) :=
  SunPrimeDensity.sunConjecture_iff_of_RH riemannHypothesis

#print axioms sun_unconditional
#print axioms sunConjectureFrom_four
#print axioms sun_three_unconditional
#print axioms sunConjecture_iff_three_range
