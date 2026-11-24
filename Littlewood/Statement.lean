import Mathlib

/-!
# Littlewood's bound for `ζ(1/2 + it)` under RH (target statement — do not change the definition)

The deliverable is `Littlewood.littlewood_of_RH` (`Littlewood/Main.lean`).

Littlewood (*On the zeros of the Riemann zeta-function*, Proc. Cambridge Philos. Soc. 22
(1924), 295–318) proved that the Riemann hypothesis implies

    |ζ(1/2 + it)| ≤ exp(C log t / log log t)    for all large t,

for some absolute constant `C`. Titchmarsh, *The Zeta-Function of Riemann* (Cambridge Tracts 26,
1930), Theorem 63 (§5.72), credits it to Littlewood (4) and Titchmarsh (3); in the second
edition of *The Theory of the Riemann Zeta-Function* it is in §14.14. The sharp constant
`C = (log 2)/2 + o(1)` is Chandee–Soundararajan, Bull. LMS 43 (2011); it is not the target here.

`formal-conjectures` has no statement of this result (searched 2026-11-24), so the statement is
fixed here. It is stated for the norm, so that no junk value of `Real.log 0` enters, and only for
`t → +∞`: `ζ(conj s) = conj ζ(s)` gives `t → -∞`. `RiemannHypothesis` is Mathlib's statement.
-/

namespace Littlewood

open Complex

/-- **Littlewood's bound**: there are constants `C` and `t₀` such that
`‖ζ(1/2 + it)‖ ≤ exp (C log t / log log t)` for every `t ≥ t₀`. -/
def LittlewoodBound : Prop :=
  ∃ C t₀ : ℝ, ∀ t : ℝ, t₀ ≤ t →
    ‖riemannZeta (1 / 2 + t * I)‖ ≤ Real.exp (C * Real.log t / Real.log (Real.log t))

end Littlewood
