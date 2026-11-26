import Mathlib

/-!
# Cramér's prime-gap theorem under RH (target statements — do not change the definitions)

Cramér (1920, *Arkiv för Mat., Astr. och Fys.* **15**, no. 5): under the Riemann hypothesis,
`p_{n+1} − p_n = O(√p_n · log p_n)`. The best explicit constant known is
Carneiro–Milinovich–Soundararajan (2019, *Comment. Math. Helv.* **94**, 533–568):
`p_{n+1} − p_n < (22/25) √p_n log p_n` for every `p_n > 3`.

`primeGap` is copied word for word from google-deepmind/formal-conjectures,
`FormalConjecturesForMathlib/NumberTheory/PrimeGap.lean`, and `CramerGapBound` is the conclusion
of `cramer_conjecture.variants.conditional_rh` in
`FormalConjectures/Wikipedia/CramerConjecture.lean` (commit `86a2f58a`), whose hypothesis is
Mathlib's `RiemannHypothesis`.

The explicit forms `PrimeInShortInterval c` and `PrimeGapExplicit c` are parametrised by the
constant; the constant proved here is recorded in the README ("Deviations from the literature").
-/

namespace Cramer

/--
The prime gap: the difference between the $n+1$-th and $n$-th prime.
-/
noncomputable def primeGap (n : ℕ) : ℕ := (n + 1).nth Nat.Prime - n.nth Nat.Prime

open scoped Asymptotics in
/-- **Cramér's conditional prime-gap bound**: `p_{n+1} − p_n = O(√p_n log p_n)`. -/
def CramerGapBound : Prop :=
  (fun n : ℕ => (primeGap n : ℝ)) =O[Filter.atTop]
    (fun n : ℕ => Real.sqrt (Nat.nth Nat.Prime n) * Real.log (Nat.nth Nat.Prime n))

/-- Explicit short-interval form with constant `c`: every interval `(x, x + c √x log x]` with
`x ≥ 2` contains a prime. -/
def PrimeInShortInterval (c : ℝ) : Prop :=
  ∀ x : ℝ, 2 ≤ x → ∃ p : ℕ, p.Prime ∧ x < p ∧ (p : ℝ) ≤ x + c * Real.sqrt x * Real.log x

/-- Explicit prime-gap form with constant `c`: `p_{n+1} − p_n ≤ c √p_n log p_n` for every `n`. -/
def PrimeGapExplicit (c : ℝ) : Prop :=
  ∀ n : ℕ, (primeGap n : ℝ) ≤
    c * Real.sqrt (Nat.nth Nat.Prime n) * Real.log (Nat.nth Nat.Prime n)

end Cramer
