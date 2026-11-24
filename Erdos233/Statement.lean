import Mathlib

/-!
# Erdős Problem 233 (target statements: do not change the definitions)

Source: google-deepmind/formal-conjectures,
[`FormalConjectures/ErdosProblems/233.lean`](https://github.com/google-deepmind/formal-conjectures/blob/d9f6ffa8dd7fc2b8b597dd1f7a824d27b12b88af/FormalConjectures/ErdosProblems/233.lean)
(commit `d9f6ffa8`), and `primeGap` from
[`FormalConjecturesForMathlib/NumberTheory/PrimeGap.lean`](https://github.com/google-deepmind/formal-conjectures/blob/86a2f58a4d7a3a0637d15d5b2ce627592b54b956/FormalConjecturesForMathlib/NumberTheory/PrimeGap.lean),
both Apache-2.0. The bodies below are copied verbatim; only the `theorem … := by sorry`
wrappers became `def … : Prop :=` so that nothing here is asserted.

* `Erdos233Statement` is `erdos_233` (Heath-Brown's conjecture `Σ_{n<N} d_n² ≪ N log² N`).
  It is **open**, also under RH, and this project does not prove it.
* `Erdos233UpperBoundStatement` is `erdos_233.variants.upper_bound`: under RH,
  `Σ_{n<N} d_n² ≪ N log⁴ N`. This is the target of `Erdos233.erdos_233_upper_bound_of_RH`.
  In the `p_n ≤ x` indexing it is Selberg's (1943) bound `Σ_{p_n ≤ x} d_n² ≪ x log³ x`,
  because `p_N ≍ N log N`.

`RiemannHypothesis` is Mathlib's statement, as in formal-conjectures.
-/

open Filter Real

/--
The prime gap: the difference between the $n+1$-th and $n$-th prime.
-/
noncomputable def primeGap (n : ℕ) : ℕ := (n + 1).nth Nat.Prime - n.nth Nat.Prime

namespace Erdos233

/--
A conjecture by Heath-Brown:
The sum of squares of the first $N$ gaps between consecutive primes behaves like $N * (log N)^2$.
-/
def Erdos233Statement : Prop :=
    (fun N => ((∑ n ∈ Finset.range N, (primeGap n) ^ 2) : ℝ)) =O[atTop] fun N => N * (log N)^2

/--
Cramér proved an upper bound of $O(N(\log N)^4)$ conditional on the Riemann hypothesis.

(The conclusion of `erdos_233.variants.upper_bound`, whose hypothesis is
`(h : RiemannHypothesis)`.)
-/
def Erdos233UpperBoundStatement : Prop :=
    (fun N => ((∑ n ∈ Finset.range N, (primeGap n) ^ 2) : ℝ)) =O[atTop] fun N => N * (log N)^4

end Erdos233
