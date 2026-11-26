import Mathlib

/-!
# Nicolas' inequality for primorials (target statement — do not change the definitions)

Nicolas (*Petites valeurs de la fonction d'Euler*, J. Number Theory 17 (1983) 375–388) proved
that the Riemann hypothesis is equivalent to `N_k/φ(N_k) > e^γ log log N_k` for every `k ≥ 1`,
where `N_k = p_1 ⋯ p_k` is the product of the first `k` primes. This repository proves the
direction RH ⇒ inequality. `RiemannHypothesis` is Mathlib's statement;
leanprover-community/riemann-hypothesis proves it as `riemannHypothesis : RiemannHypothesis`.

formal-conjectures has no statement of Nicolas' criterion. `kthPrimorial` is copied verbatim
from formal-conjectures (`FormalConjecturesForMathlib/Data/Nat/Prime/Nth.lean`,
`Nat.kthPrimorial`, commit `86a2f58a`, Apache-2.0), placed in the `Nicolas` namespace.
-/

namespace Nicolas

/-- The $k$-th primorial $p_k\# = \prod_{i < k} p_{i+1}$, defined as the product of the first $k$
prime numbers. Unlike `_root_.primorial n` (which takes the product of primes $\le n$),
`Nat.kthPrimorial k` is indexed by the number of prime factors $k$. -/
noncomputable def kthPrimorial (k : ℕ) : ℕ :=
  ∏ i ∈ Finset.range k, Nat.nth Nat.Prime i

/-- **Nicolas' inequality**: `N_k / φ(N_k) > e^γ log log N_k` for every `k ≥ 1`. -/
def NicolasStatement : Prop :=
  ∀ k : ℕ, 1 ≤ k →
    Real.exp Real.eulerMascheroniConstant * Real.log (Real.log (kthPrimorial k))
      < (kthPrimorial k : ℝ) / (Nat.totient (kthPrimorial k) : ℝ)

end Nicolas
