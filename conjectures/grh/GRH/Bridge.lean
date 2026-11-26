import Main

/-!
# Bridge from the vendored grh-lean proof to our `Unconditional/` files

Not part of the vendored tree (`src/`): this file belongs to our port.

`src/Main.lean` (lsernau/grh-lean, compact edition) proves, at the top level,

* `riemannHypothesis : RiemannHypothesis` (Mathlib's statement), and
* `LFunction_ne_zero_of_half_lt_re : DirichletLNonvanishingRightOfHalf`,

where `DirichletLNonvanishingRightOfHalf` is the definition in `src/Statements.lean`. That
definition is word for word the one in leanprover-community/riemann-hypothesis
`src/Statements.lean`, and our projects' copies (`Erdos985.DirichletLNonvanishingRightOfHalf`)
have the same body, so they are definitionally equal and the theorem discharges them as it
stands. An `Unconditional/` file therefore switches source by replacing `import Main` (from
riemann-hypothesis) with `import GRH.Bridge`; nothing else changes.

The `example`s below pin the two forms the `Unconditional/` files use.
-/

example : RiemannHypothesis := riemannHypothesis

example : DirichletLNonvanishingRightOfHalf := LFunction_ne_zero_of_half_lt_re

/-- The body of `DirichletLNonvanishingRightOfHalf`, spelled out: a copy of this body under
another name (such as `Erdos985.DirichletLNonvanishingRightOfHalf`) is discharged by
`LFunction_ne_zero_of_half_lt_re` directly. -/
example : ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (s : ℂ),
    1 / 2 < s.re → (χ ≠ 1 ∨ s ≠ 1) → DirichletCharacter.LFunction χ s ≠ 0 :=
  LFunction_ne_zero_of_half_lt_re
