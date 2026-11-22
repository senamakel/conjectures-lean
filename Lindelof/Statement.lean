import Erdos985.Statement

/-!
# The Lindelöf hypothesis (target statements — do not change the definitions)

The deliverables are `Lindelof.lindelof_of_RH` (`Lindelof/Main.lean`) and, as a stretch goal,
`Lindelof.dirichletLindelof_of_GRH` (`Lindelof/Dirichlet.lean`).

Lindelöf (1908) conjectured that `ζ(1/2 + it) = O(|t|^ε)` for every `ε > 0`. Littlewood (1912)
proved that it follows from the Riemann hypothesis (Titchmarsh, *The Theory of the Riemann
Zeta-Function*, 2nd ed., §14.2).

`RiemannHypothesis` is Mathlib's statement; leanprover-community/riemann-hypothesis proves it
as `riemannHypothesis : RiemannHypothesis`. `DirichletLNonvanishingRightOfHalf` is copied word
for word from that repository's `src/Statements.lean` (via `Erdos985.Statement`) and is proved
there as `LFunction_ne_zero_of_half_lt_re`.

Only `t → +∞` is stated: `ζ(conj s) = conj ζ(s)` gives `t → -∞` for free.
-/

namespace Lindelof

open Complex Filter Asymptotics

/-- **The Lindelöf hypothesis**: for every `ε > 0`, `ζ(1/2 + it) = O(t^ε)` as `t → ∞`. -/
def LindelofHypothesis : Prop :=
  ∀ ε : ℝ, 0 < ε →
    (fun t : ℝ => ‖riemannZeta (1 / 2 + t * I)‖) =O[atTop] fun t : ℝ => t ^ ε

/-- The Lindelöf hypothesis for every Dirichlet L-function, in the `t`-aspect (stretch goal):
for every modulus `N`, character `χ` and `ε > 0`, `L(1/2 + it, χ) = O(t^ε)` as `t → ∞`. -/
def DirichletLindelofHypothesis : Prop :=
  ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (ε : ℝ), 0 < ε →
    (fun t : ℝ => ‖DirichletCharacter.LFunction χ (1 / 2 + t * I)‖) =O[atTop]
      fun t : ℝ => t ^ ε

end Lindelof
