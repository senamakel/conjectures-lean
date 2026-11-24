import Mathlib

/-!
# Cramér's mean-square theorem under RH (target statements, Round 5 — do not change)

H. Cramér, *Ein Mittelwertsatz in der Primzahltheorie*, Math. Z. **12** (1922), 147–153:
under the Riemann hypothesis the mean square of `(ψ(x) − x)/√x` is bounded. In the forms used
by Montgomery–Vaughan, *Multiplicative Number Theory I* (2007), Theorem 13.5 and §13.1,
and by Brent–Platt–Trudgian, *J. Number Theory* **238** (2022), 740–762, eq. (1):

* `∫_X^{2X} (ψ(x) − x)² dx ≪ X²`;
* `∫_1^X (ψ(x) − x)² dx ≪ X²`;
* `∫_1^X (ψ(x) − x)²/x² dx ≪ log X` (Montgomery–Vaughan Theorem 13.6 and Exercise 13.1.1.3
  give the asymptotic `∼ (Σ_ρ m_ρ/|ρ|²) log X`; only the upper bound is stated here).

No formal-conjectures statement exists (searched 2026-11-24 at `9097e2f9`). `ψ` is Mathlib's
`Chebyshev.psi` (`ψ x = Σ_{0 < n ≤ x} Λ(n)`). The hypothesis of each theorem proving these is
Mathlib's `RiemannHypothesis`.
-/

namespace Cramer

open Chebyshev

open scoped Asymptotics in
/-- **Cramér (1922)**, dyadic form: `∫_X^{2X} (ψ(x) − x)² dx = O(X²)`. -/
def CramerDyadicMeanSquare : Prop :=
  (fun X : ℝ => ∫ x in X..2 * X, (ψ x - x) ^ 2) =O[Filter.atTop] (fun X : ℝ => X ^ 2)

open scoped Asymptotics in
/-- **Cramér (1922)**: `∫_1^X (ψ(x) − x)² dx = O(X²)`. -/
def CramerMeanSquare : Prop :=
  (fun X : ℝ => ∫ x in (1 : ℝ)..X, (ψ x - x) ^ 2) =O[Filter.atTop] (fun X : ℝ => X ^ 2)

open scoped Asymptotics in
/-- Logarithmic form: `∫_1^X ((ψ(x) − x)/x)² dx = O(log X)`. -/
def CramerLogMeanSquare : Prop :=
  (fun X : ℝ => ∫ x in (1 : ℝ)..X, ((ψ x - x) / x) ^ 2) =O[Filter.atTop] Real.log

end Cramer
