import Mathlib

/-!
# Statements: two monotonicity conjectures of Zhi-Wei Sun on `π(x)`

Fixed target statements. Do not edit them to make a proof go through.

Source: Z.-W. Sun, *Problems on combinatorial properties of primes*, arXiv:1402.6641 (v12,
2016-02-25), in: M. Kaneko, S. Kanemitsu and J. Liu (eds.), *Number Theory: Plowing and
Starring through High Wave Forms*, Ser. Number Theory Appl. 11, World Sci., 2015, pp. 169–187.

* Conjecture 2.7(i) (dated 2014-02-17 there): "For any integer `n > 4` and `k = 1, …, n`, we have
  `π(kn)^{1/k} > π((k + 1)n)^{1/(k+1)}`." The same statement is OEIS A238165, comment
  "(ii) For any integer n > 4, the sequence pi(k*n)^(1/k) (k = 1, ..., n) is strictly
  decreasing"; Sun's paper form also covers the step from `k = n` to `n + 1`.
* Conjecture 2.14(ii) (dated 2014-02-17 there): "The sequence `π(n²)^{1/n}` (`n = 3, 4, …`) is
  strictly decreasing." The same statement is OEIS A038107, Sun's comment of Feb 17 2014:
  "(i) The sequence a(n)^(1/n) (n = 3, 4, ...) is strictly decreasing (to the limit 1)", where
  `a(n)` is the number of primes `< n²`.

formal-conjectures (clone at `9097e2f`) has no statement of either. Its
`FormalConjectures/OEIS/38107.lean` defines A038107 as `OeisA38107.a` and states only Sun's
2015 conjecture on fractional parts; `a` below is copied from it word for word.
-/

open scoped Nat.Prime
open Filter Topology

namespace SunPi

/-- Sun, arXiv:1402.6641, Conjecture 2.7(i): for `n > 4` and `1 ≤ k ≤ n`,
`π(kn)^{1/k} > π((k+1)n)^{1/(k+1)}`. -/
def SunConjecture_2_7_i : Prop :=
  ∀ n : ℕ, 4 < n → ∀ k : ℕ, 1 ≤ k → k ≤ n →
    (π ((k + 1) * n) : ℝ) ^ ((1 : ℝ) / (k + 1)) < (π (k * n) : ℝ) ^ ((1 : ℝ) / k)

/-- OEIS A238165, conjecture (ii): for `n > 4`, `k ↦ π(kn)^{1/k}` is strictly decreasing on
`k = 1, …, n`. -/
def OeisA238165_ii : Prop :=
  ∀ n : ℕ, 4 < n →
    StrictAntiOn (fun k : ℕ => (π (k * n) : ℝ) ^ ((1 : ℝ) / k)) (Set.Icc 1 n)

/-- Sun, arXiv:1402.6641, Conjecture 2.14(ii): `π(n²)^{1/n}` is strictly decreasing for
`n ≥ 3`. -/
def SunConjecture_2_14_ii : Prop :=
  ∀ n : ℕ, 3 ≤ n →
    (π ((n + 1) ^ 2) : ℝ) ^ ((1 : ℝ) / (n + 1)) < (π (n ^ 2) : ℝ) ^ ((1 : ℝ) / n)

/-- Number of primes strictly less than $n^2$ (OEIS A038107). Copied verbatim from
formal-conjectures `FormalConjectures/OEIS/38107.lean`, `OeisA38107.a`. -/
def a (n : ℕ) : ℕ := (Nat.primesBelow (n ^ 2)).card

/-- OEIS A038107, Sun's conjecture (i) of Feb 17 2014: `a(n)^{1/n}` (`n = 3, 4, …`) is strictly
decreasing, with limit 1. -/
def OeisA038107_i : Prop :=
  StrictAntiOn (fun n : ℕ => (a n : ℝ) ^ ((1 : ℝ) / n)) (Set.Ici 3) ∧
    Tendsto (fun n : ℕ => (a n : ℝ) ^ ((1 : ℝ) / n)) atTop (𝓝 1)

end SunPi
