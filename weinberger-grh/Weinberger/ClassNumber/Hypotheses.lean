import Weinberger.Statement

/-!
# Cited inputs for the class number one problem (tier H)

Two classical facts about imaginary quadratic fields that the Mathlib pin cannot yet reach from
`NumberField.classNumber (AdjoinRoot (X ^ 2 - C d))`. They are explicit hypotheses of
`Weinberger.starkHeegner_of_GRH`, never `sorry`s. See `docs/SCOPING.md` for what proving them
in Lean would take.

* `ClassNumberOneNorms`: if `ℚ(√d)` has class number one, every prime `p` with an ideal of norm
  `p` is the norm of an integer. Write `ω = (1 + √d)/2` when `d ≡ 1 (mod 4)` and `ω = √d`
  otherwise. If `p ∣ N(t + ω)`, the ideal `(p, t + ω)` has norm `p`; when it is principal, its
  generator `u + vω` has norm `p`. Here `N(t + ω) = t² + t + (1 − d)/4` resp. `t² − d`, and
  `N(u + vω) = u² + uv + ((1 − d)/4) v²` resp. `u² − d v²`.
* `HeegnerClassNumberOne`: the nine fields `ℚ(√d)`, `d ∈ {−1, −2, −3, −7, −11, −19, −43, −67,
  −163}`, have class number one (Gauss's table; a Minkowski-bound computation for each field).
-/

namespace Weinberger

open ClassNumberProblem

/-- Class number one makes every prime of degree one principal, hence a norm. -/
def ClassNumberOneNorms : Prop :=
  ∀ d : ℤ, Squarefree d → d < 0 → IsClassNumberOne d → ∀ p : ℕ, p.Prime → ∀ t : ℤ,
    (d % 4 = 1 → (p : ℤ) ∣ t ^ 2 + t + (1 - d) / 4 →
      ∃ u v : ℤ, u ^ 2 + u * v + (1 - d) / 4 * v ^ 2 = p) ∧
    (d % 4 ≠ 1 → (p : ℤ) ∣ t ^ 2 - d → ∃ u v : ℤ, u ^ 2 - d * v ^ 2 = p)

/-- The nine Heegner fields have class number one. -/
def HeegnerClassNumberOne : Prop :=
  ∀ d ∈ ([-1, -2, -3, -7, -11, -19, -43, -67, -163] : List ℤ), IsClassNumberOne d

end Weinberger
