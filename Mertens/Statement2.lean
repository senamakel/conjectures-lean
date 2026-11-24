import Mertens.Statement

/-!
# Target statements, second batch (fixed once written; see the conjectures tracker, rule 3)

Three further classical consequences of RH, each equivalent to RH (only the RH ⇒ direction is
in scope). None has a formal-conjectures counterpart (checked against
google-deepmind/formal-conjectures `9097e2f`, 2026-11-24: no entry for the Möbius Dirichlet
series, for `∑ λ(n)` bounds, or for Farey-sequence discrepancy), so they are fixed here.

* `moebiusPartial`/`MoebiusSeriesConverges`: `∑ μ(n) n^{-s}` converges to `1/ζ(s)` for every
  `Re s > 1/2` (Littlewood, C. R. Acad. Sci. Paris 154 (1912) 263–266; see Titchmarsh, *The
  Theory of the Riemann Zeta-Function*, ch. 14). The series converges only conditionally for
  `1/2 < Re s ≤ 1`, so its sum is the limit of the partial sums, not a `tsum` (which would be
  Mathlib's junk value `0`). At `s = 1` Mathlib's `riemannZeta 1` is a junk value, not the
  pole, so the statement there is the true value `∑ μ(n)/n = 0`.
* `liouvilleSum`/`LiouvilleBound`: `L(x) = ∑_{n ≤ x} λ(n) = O(x^{1/2+ε})` for every `ε > 0`, with
  Mathlib's `ArithmeticFunction.liouville`. Equivalent to RH through
  `ζ(2s)/ζ(s) = s ∫₁^∞ L(t) t^{-s-1} dt`; stated e.g. in Humphries, J. Number Theory 133 (2013)
  545–582 (arXiv:1108.1524). The RH ⇒ bound direction follows from Littlewood's Mertens bound
  through `λ = 1_{squares} * μ`.
* `farey`, `fareyFrac`, `franelL1`/`FranelLandauBound`, `franelL2`/`FranelBound`: with
  `F_N = (f_1 < ⋯ < f_A)` the Farey fractions of order `N` in `(0, 1]` and `A = |F_N|`,
  `∑_k |f_k − k/A| = O(N^{1/2+ε})` (Landau, Göttinger Nachrichten 1924, 202–206) and
  `∑_k (f_k − k/A)² = O(N^{−1+ε})` (Franel, Göttinger Nachrichten 1924, 198–201).
-/

namespace Mertens

open Filter Topology Asymptotics ArithmeticFunction
open scoped ArithmeticFunction.Moebius

/-- Partial sums `∑_{n < N} μ(n) n^{-s}` of the Möbius Dirichlet series. -/
noncomputable def moebiusPartial (s : ℂ) (N : ℕ) : ℂ :=
  ∑ n ∈ Finset.range N, (μ n : ℂ) / (n : ℂ) ^ s

/-- **Littlewood (1912)**: for every `Re s > 1/2` the partial sums of `∑ μ(n) n^{-s}` converge to
`1/ζ(s)`; at `s = 1` (where Mathlib's `riemannZeta 1` is a junk value) they converge to `0`. -/
def MoebiusSeriesConverges : Prop :=
  (∀ s : ℂ, 1 / 2 < s.re → s ≠ 1 → Tendsto (moebiusPartial s) atTop (𝓝 (riemannZeta s)⁻¹)) ∧
  Tendsto (moebiusPartial 1) atTop (𝓝 0)

/-- The summatory Liouville function `L(x) = ∑_{1 ≤ n ≤ x} λ(n)`. -/
noncomputable def liouvilleSum (x : ℝ) : ℤ := ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, liouville n

/-- `L(x) = O(x^{1/2+ε})` for every `ε > 0`. -/
def LiouvilleBound : Prop :=
  ∀ ε : ℝ, 0 < ε → (fun x : ℝ => (liouvilleSum x : ℝ)) =O[atTop] fun x : ℝ => x ^ (1 / 2 + ε)

/-- The Farey fractions of order `N` in `(0, 1]`: the rationals `p/q` with `1 ≤ p ≤ q ≤ N`. -/
def farey (N : ℕ) : Finset ℚ :=
  ((Finset.Icc 1 N ×ˢ Finset.Icc 1 N).filter fun pq => pq.1 ≤ pq.2).image
    fun pq => (pq.1 : ℚ) / pq.2

/-- `fareyFrac N i` is `f_{i+1}`, the `(i+1)`-st smallest Farey fraction of order `N`. -/
def fareyFrac (N : ℕ) (i : Fin (farey N).card) : ℚ := (farey N).orderEmbOfFin rfl i

/-- `∑_{k=1}^{A} |f_k − k/A|` with `A = |F_N|`. -/
noncomputable def franelL1 (N : ℕ) : ℝ :=
  ∑ i : Fin (farey N).card, |(fareyFrac N i : ℝ) - ((i : ℕ) + 1 : ℝ) / (farey N).card|

/-- `∑_{k=1}^{A} (f_k − k/A)²` with `A = |F_N|`. -/
noncomputable def franelL2 (N : ℕ) : ℝ :=
  ∑ i : Fin (farey N).card, ((fareyFrac N i : ℝ) - ((i : ℕ) + 1 : ℝ) / (farey N).card) ^ 2

/-- **Landau (1924)**: `∑_k |f_k − k/A| = O(N^{1/2+ε})` for every `ε > 0`. -/
def FranelLandauBound : Prop :=
  ∀ ε : ℝ, 0 < ε → franelL1 =O[atTop] fun N : ℕ => (N : ℝ) ^ (1 / 2 + ε)

/-- **Franel (1924)**: `∑_k (f_k − k/A)² = O(N^{−1+ε})` for every `ε > 0`. -/
def FranelBound : Prop :=
  ∀ ε : ℝ, 0 < ε → franelL2 =O[atTop] fun N : ℕ => (N : ℝ) ^ (-1 + ε)

end Mertens
