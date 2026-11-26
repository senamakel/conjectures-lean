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

end Abundant
