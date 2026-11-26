import Mathlib

/-!
# The least prime in a residue class (target statements — do not change the definitions)

E. Bach and J. Sorenson, *Explicit bounds for primes in residue classes*, Math. Comp. 65
(1996), 1717–1735. Assuming the Extended Riemann Hypothesis, the abstract states: if
`gcd(m, q) = 1`, the least prime `p ≡ m (mod q)` is less than `2 (q log q)²`; asymptotically
`p ≤ (1 + o(1)) (φ(q) log q)²`. Unconditionally the best results are Linnik-type bounds
`p ≪ q^L` (Xylouris: `L = 5`).

`BachSorensonBound c` is that statement with the constant `2` replaced by a parameter `c`;
`BachSorensonBound 2` is the literature statement. The modulus is required to satisfy `2 ≤ q`:
for `q = 1` the right-hand side `c (1 · log 1)² = 0` and no prime is below it, so the paper's
statement is read for non-trivial moduli.
-/

namespace BachSorenson

/-- For every modulus `q ≥ 2` and every `a` coprime to `q` there is a prime `p ≡ a (mod q)` with
`p < c (q log q)²`. -/
def BachSorensonBound (c : ℝ) : Prop :=
  ∀ q a : ℕ, 2 ≤ q → a.Coprime q →
    ∃ p : ℕ, p.Prime ∧ p ≡ a [MOD q] ∧ (p : ℝ) < c * ((q : ℝ) * Real.log q) ^ 2

-- `bachSorenson_of_GRH : DirichletLNonvanishingRightOfHalf → BachSorensonBound (7 / 2)` is proved in
-- `BachSorenson/Main.lean`. `BachSorensonBound 2` (Bach–Sorenson's constant) is not proved.

end BachSorenson
