import Schoenfeld.Statement

/-!
# The finite ranges (tier H)

Below the ranges covered analytically or by PsiCert, Schoenfeld (1976, proof of Theorem 10 and
Corollary 1) checks his three bounds numerically: Gram's table of `ψ` for
`73.2 ≤ x < 1075`, the Rosser–Walker tables for `θ` on `599 ≤ x < 1200`, and the
Appel–Rosser and Brent tables for `π − li` on `2657 ≤ x ≤ 5·10⁹`. Here the three finite
ranges that remain are smaller:

* `PsiSmallRange`: `|ψ(x) − x| < √x log² x/(8π)` for `73.2 ≤ x ≤ 1500`;
* `ThetaSmallRange`: `|θ(x) − x| < √x log² x/(8π)` for `599 ≤ x ≤ 3·10⁴`;
* `PiSmallRange`: `|π(x) − li(x)| < √x log x/(8π)` for `2657 ≤ x ≤ 4·10⁵`.

Each is Schoenfeld's own statement restricted to a compact range: a finite computation over
the prime powers below the upper end (about 240, 3250 and 33,860 primes respectively).
-/

namespace Schoenfeld

open Chebyshev Real

/-- `|ψ(x) − x| < √x log² x/(8π)` on `[73.2, 1500]`. -/
def PsiSmallRange : Prop :=
  ∀ x : ℝ, 73.2 ≤ x → x ≤ 1500 → |ψ x - x| < 1 / (8 * π) * (√x * Real.log x ^ 2)

/-- `|θ(x) − x| < √x log² x/(8π)` on `[599, 3·10⁴]`. -/
def ThetaSmallRange : Prop :=
  ∀ x : ℝ, 599 ≤ x → x ≤ 30000 → |θ x - x| < 1 / (8 * π) * (√x * Real.log x ^ 2)

/-- `|π(x) − li(x)| < √x log x/(8π)` on `[2657, 4·10⁵]`. -/
def PiSmallRange : Prop :=
  ∀ x : ℝ, 2657 ≤ x → x ≤ 400000 →
    |(Nat.primeCounting ⌊x⌋₊ : ℝ) - Real.logIntegral x| < 1 / (8 * π) * (√x * Real.log x)

end Schoenfeld
