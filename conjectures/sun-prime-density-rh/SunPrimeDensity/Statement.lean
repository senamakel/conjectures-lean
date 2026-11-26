import Mathlib

/-!
# Sun's conjecture on `π(n^k)/n^k` (OEIS A038098)

Zhi-Wei Sun (17 October 2015, OEIS A038098; MathOverflow 301662): for every integer `k > 2`
the sequence `π(n^k)/n^k` (`n = 2, 3, …`) is strictly decreasing.

`SunConjecture` is the statement of `OeisA38098.conjecture1` in
[google-deepmind/formal-conjectures](https://github.com/google-deepmind/formal-conjectures),
`FormalConjectures/OEIS/38098.lean` at commit `9097e2f` (category `research open`), copied word
for word with the binders moved under a `∀`. `SunConjectureFrom k₀` is the same statement for
the exponents `k ≥ k₀`.

This file holds the targets only; it is not edited to make a proof go through.
-/

namespace SunPrimeDensity

/-- Sun's conjecture (i) of OEIS A038098: for every `k > 2` and `n ≥ 2`,
`π((n+1)^k)/(n+1)^k < π(n^k)/n^k` (formal-conjectures `OeisA38098.conjecture1`, verbatim). -/
def SunConjecture : Prop :=
  ∀ (k : ℕ) (_hk : 2 < k) (n : ℕ) (_hn : 2 ≤ n),
    (Nat.primeCounting ((n + 1) ^ k) : ℚ) / ((n + 1) ^ k : ℚ) <
    (Nat.primeCounting (n ^ k) : ℚ) / (n ^ k : ℚ)

/-- Sun's conjecture for the exponents `k ≥ k₀`. -/
def SunConjectureFrom (k₀ : ℕ) : Prop :=
  ∀ (k : ℕ) (_hk : k₀ ≤ k) (n : ℕ) (_hn : 2 ≤ n),
    (Nat.primeCounting ((n + 1) ^ k) : ℚ) / ((n + 1) ^ k : ℚ) <
    (Nat.primeCounting (n ^ k) : ℚ) / (n ^ k : ℚ)

/-- Conjecture (ii) of OEIS A038098 (formal-conjectures `OeisA38098.conjecture2`, verbatim):
the numbers `π(n²)/n²` are pairwise distinct, and decrease for `n > 15646`. Not proved here. -/
def SunConjectureSquares : Prop :=
  (∀ m n : ℕ, 1 ≤ m → 1 ≤ n →
      (Nat.primeCounting (m ^ 2) : ℚ) / (m ^ 2 : ℚ) =
      (Nat.primeCounting (n ^ 2) : ℚ) / (n ^ 2 : ℚ) → m = n) ∧
    (∀ n : ℕ, 15646 < n →
      (Nat.primeCounting ((n + 1) ^ 2) : ℚ) / ((n + 1) ^ 2 : ℚ) <
      (Nat.primeCounting (n ^ 2) : ℚ) / (n ^ 2 : ℚ))

/-- `SunConjectureFrom 3` is `SunConjecture`. -/
theorem sunConjecture_iff : SunConjecture ↔ SunConjectureFrom 3 :=
  ⟨fun h k hk n hn => h k hk n hn, fun h k hk n hn => h k hk n hn⟩

end SunPrimeDensity
