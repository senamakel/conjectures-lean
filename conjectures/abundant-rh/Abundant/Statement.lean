import Nicolas.Statement

/-!
# Target statements (fixed: do not change these definitions to make a proof go through)

## Solé–Planat

P. Solé and M. Planat, *Extreme values of the Dedekind Ψ function*, J. Comb. Number Theory 3
(2011), no. 1, 1–6, arXiv:1011.1825 (abstract and main theorem read on arXiv). With
`Ψ(n) = n ∏_{p ∣ n} (1 + 1/p)` and `R(n) = Ψ(n)/(n log log n)`, they prove that
`R(N_n) > e^γ/ζ(2)` for every `n ≥ 3` is equivalent to the Riemann hypothesis, where
`N_n = p_1 ⋯ p_n` is the primorial of order `n`. `SolePlanatStatement` is that inequality.
formal-conjectures has no statement of it. `N_n` is nicolas-rh's `Nicolas.kthPrimorial n`
(itself copied verbatim from formal-conjectures' `Nat.kthPrimorial`), imported, not restated.
-/

namespace Abundant

/-- The Dedekind psi function `Ψ(n) = n ∏_{p ∣ n} (1 + 1/p)`, real-valued. -/
noncomputable def dedekindPsi (n : ℕ) : ℝ :=
  n * ∏ p ∈ n.primeFactors, (1 + 1 / (p : ℝ))

/-- Solé–Planat's ratio `R(n) = Ψ(n)/(n log log n)`. -/
noncomputable def solePlanatRatio (n : ℕ) : ℝ :=
  dedekindPsi n / (n * Real.log (Real.log n))

/-- **Solé–Planat** (2011): `R(N_n) > e^γ/ζ(2)` for every `n ≥ 3`, `N_n` the `n`-th primorial.
`riemannZeta 2` is complex-valued in Mathlib; its real part is `ζ(2) = π²/6`. -/
def SolePlanatStatement : Prop :=
  ∀ n : ℕ, 3 ≤ n →
    Real.exp Real.eulerMascheroniConstant / (riemannZeta 2).re
      < solePlanatRatio (Nicolas.kthPrimorial n)

/-! ## Extremely abundant numbers

S. Nazardonyavi and S. Yakubovich, *Extremely abundant numbers and the Riemann hypothesis*,
J. Integer Seq. 17 (2014), Article 14.2.8 (arXiv:1211.2147, read in v3: Definition 2.1 and
Theorem 2.4; Definition 3 and Theorem 7 in the journal numbering, not checked against the
journal PDF). With `f(n) = σ(n)/(n log log n)`, `n` is *extremely abundant* if `n = 10080`, or
`n > 10080` and `f(m) < f(n)` for every `10080 ≤ m < n`. They prove that RH holds if and only if
there are infinitely many extremely abundant numbers. No formal-conjectures entry exists. -/

open ArithmeticFunction in
open scoped ArithmeticFunction.sigma in
/-- Robin's ratio `f(n) = σ(n)/(n log log n)` (Caveney–Nicolas–Sondow's `G(n)`). -/
noncomputable def robinRatio (n : ℕ) : ℝ :=
  (σ 1 n : ℝ) / (n * Real.log (Real.log n))

/-- Nazardonyavi–Yakubovich, Definition 2.1: extremely abundant numbers. -/
def IsExtremelyAbundant (n : ℕ) : Prop :=
  n = 10080 ∨ (10080 < n ∧ ∀ m : ℕ, 10080 ≤ m → m < n → robinRatio m < robinRatio n)

/-- Nazardonyavi–Yakubovich, Theorem 2.4 (the RH direction): there are infinitely many
extremely abundant numbers. -/
def ExtremelyAbundantInfinite : Prop :=
  {n : ℕ | IsExtremelyAbundant n}.Infinite

/-! ## Extraordinary numbers

G. Caveney, J.-L. Nicolas and J. Sondow, *Robin's theorem, primes, and a new elementary
reformulation of the Riemann hypothesis*, Integers 11 (2011), A33 (arXiv:1110.5078, read in v2):
with `G(n) = σ(n)/(n log log n)` (`robinRatio`), a positive integer `N` is *extraordinary* if
`N` is composite and (i) `G(N) ≥ G(N/p)` for every prime factor `p` of `N`, and (ii)
`G(N) ≥ G(aN)` for every multiple `aN` of `N` (Definition 1). Theorem 5: RH holds if and only if
`4` is the only extraordinary number. No formal-conjectures entry exists. -/

/-- Caveney–Nicolas–Sondow, Definition 1: extraordinary numbers. -/
def IsExtraordinary (N : ℕ) : Prop :=
  (1 < N ∧ ¬ N.Prime) ∧
    (∀ p : ℕ, p.Prime → p ∣ N → robinRatio (N / p) ≤ robinRatio N) ∧
    (∀ a : ℕ, 1 ≤ a → robinRatio (a * N) ≤ robinRatio N)

/-- Caveney–Nicolas–Sondow, Theorem 5 (the RH direction): `4` is the only extraordinary
number. -/
def FourOnlyExtraordinary : Prop :=
  ∀ N : ℕ, IsExtraordinary N ↔ N = 4

end Abundant
