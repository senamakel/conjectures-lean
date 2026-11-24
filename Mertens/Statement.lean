import Mathlib

/-!
# Target statements (fixed once written; see the conjectures tracker, rule 3)

None of these statements has a formal-conjectures counterpart (checked against
google-deepmind/formal-conjectures `86a2f58`, 2026-11-24: no Mertens, Redheffer, Riesz or
Hardy–Littlewood entry), so they are fixed here.

* `mertens x = ∑_{n ≤ x} μ(n)`, the Mertens function.
* `MertensBound`: `M(x) = O(x^{1/2+ε})` for every `ε > 0` (Littlewood, C. R. Acad. Sci. Paris 154
  (1912) 263–266: this follows from RH; the converse also holds but is not in scope).
* `InvZetaBound`: `1/ζ(s) = O_{ε,δ}(|t|^ε)` uniformly on `Re s ≥ 1/2 + δ`, `|Im s| ≥ 1`
  (Titchmarsh, *The Theory of the Riemann Zeta-Function*, §14.2, (14.2.6)).
* `riesz`/`RieszBound`: the Riesz function `∑_{k ≥ 1} (-1)^{k+1} x^k / ((k-1)! ζ(2k))` is
  `O(x^{1/4+ε})` (M. Riesz, Acta Math. 40 (1916) 185–190).
* `hardyLittlewood`/`HardyLittlewoodBound`: `∑_n μ(n)/n · exp(-x/n²) = O(x^{-1/4+ε})`
  (Hardy–Littlewood, Acta Math. 41 (1916) 119–196, §2.5).
* `redheffer`/`RedhefferBound`: Redheffer's matrix (`R_{ij} = 1` if `j = 1` or `i ∣ j`, else `0`),
  `det R_n = M(n)` (Redheffer 1977), hence `det R_n = O(n^{1/2+ε})`.

`RiemannHypothesis` is Mathlib's statement; it enters the main library only as a hypothesis.
-/

namespace Mertens

open Filter Asymptotics ArithmeticFunction
open scoped ArithmeticFunction.Moebius

/-- The Mertens function `M(x) = ∑_{1 ≤ n ≤ x} μ(n)`. -/
noncomputable def mertens (x : ℝ) : ℤ := ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, μ n

/-- **Littlewood's bound**: `M(x) = O(x^{1/2+ε})` for every `ε > 0`. -/
def MertensBound : Prop :=
  ∀ ε : ℝ, 0 < ε → (fun x : ℝ => (mertens x : ℝ)) =O[atTop] fun x : ℝ => x ^ (1 / 2 + ε)

/-- `1/ζ(s) ≪_{ε,δ} |t|^ε` uniformly for `Re s ≥ 1/2 + δ`, `|t| ≥ 1`. -/
def InvZetaBound : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ δ : ℝ, 0 < δ → ∃ C : ℝ, ∀ s : ℂ, 1 / 2 + δ ≤ s.re → 1 ≤ |s.im| →
    ‖(riemannZeta s)⁻¹‖ ≤ C * |s.im| ^ ε

/-- The Riesz function `∑_{k ≥ 1} (-1)^{k+1} x^k / ((k-1)! ζ(2k))`, indexed by `j = k - 1`. -/
noncomputable def riesz (x : ℝ) : ℝ :=
  ∑' j : ℕ, (-1 : ℝ) ^ j * x ^ (j + 1) /
    ((j.factorial : ℝ) * (riemannZeta (2 * ((j : ℂ) + 1))).re)

/-- **Riesz's bound**: the Riesz function is `O(x^{1/4+ε})` for every `ε > 0`. -/
def RieszBound : Prop :=
  ∀ ε : ℝ, 0 < ε → riesz =O[atTop] fun x : ℝ => x ^ (1 / 4 + ε)

/-- The Hardy–Littlewood sum `∑_n μ(n)/n · exp(-x/n²)`. -/
noncomputable def hardyLittlewood (x : ℝ) : ℝ :=
  ∑' n : ℕ, (μ n : ℝ) / n * Real.exp (-x / (n : ℝ) ^ 2)

/-- **Hardy–Littlewood's bound**: `∑_n μ(n)/n · exp(-x/n²) = O(x^{-1/4+ε})` for every `ε > 0`. -/
def HardyLittlewoodBound : Prop :=
  ∀ ε : ℝ, 0 < ε → hardyLittlewood =O[atTop] fun x : ℝ => x ^ (-1 / 4 + ε)

/-- Redheffer's `n × n` matrix, 1-indexed: entry `(i, j)` is `1` if `j = 1` or `i ∣ j`, else `0`. -/
def redheffer (n : ℕ) : Matrix (Fin n) (Fin n) ℤ := fun i j =>
  if (j : ℕ) = 0 ∨ ((i : ℕ) + 1) ∣ ((j : ℕ) + 1) then 1 else 0

/-- `det R_n = O(n^{1/2+ε})` for every `ε > 0`. -/
def RedhefferBound : Prop :=
  ∀ ε : ℝ, 0 < ε →
    (fun n : ℕ => ((redheffer n).det : ℝ)) =O[atTop] fun n : ℕ => (n : ℝ) ^ (1 / 2 + ε)

end Mertens
