import Mathlib

/-!
# Green's problem 75 ⇒ its constant form

Both statements are copied word for word from formal-conjectures (commit `9097e2f`),
`FormalConjectures/GreensOpenProblems/75.lean`, with the definitions `Green75.cross`,
`Green75.leftCount`, `Green75.rightCount` and `Green75.imbalance` from the same file
(Apache-2.0, © 2026 The Formal Conjectures Authors):

* `Green75.green_75` (research open), stated here as `Green75Statement`: every finite planar set
  with at least two points has a line through two of its points whose sides differ by at most `100`;
* `Green75.green_75.variants.exists_constant` (research open), stated here as
  `Green75ExistsConstant`: the same with some constant `C` in place of `100`.

The implication is the one the docstring of `exists_constant` records ("`green_75` implies it with
`C = 100`"); it is a specialisation.
-/

open scoped Finset

namespace Implications.Combinatorics.Green75

/-- Verbatim from formal-conjectures `9097e2f`, `Green75.cross`:
the cross product $(q - p) \times (x - p)$. -/
def cross (p q x : ℝ × ℝ) : ℝ :=
  (q.1 - p.1) * (x.2 - p.2) - (q.2 - p.2) * (x.1 - p.1)

/-- Verbatim from formal-conjectures `9097e2f`, `Green75.leftCount`: the number of points of `X`
strictly to the left of the line from `p` to `q`. -/
noncomputable def leftCount (X : Finset (ℝ × ℝ)) (p q : ℝ × ℝ) : ℕ :=
  #{x ∈ X | 0 < cross p q x}

/-- Verbatim from formal-conjectures `9097e2f`, `Green75.rightCount`: the number of points of `X`
strictly to the right of the line from `p` to `q`. -/
noncomputable def rightCount (X : Finset (ℝ × ℝ)) (p q : ℝ × ℝ) : ℕ :=
  #{x ∈ X | cross p q x < 0}

/-- Verbatim from formal-conjectures `9097e2f`, `Green75.imbalance`: the absolute difference
between the numbers of points of `X` on the two sides of the line through `p` and `q`. -/
noncomputable def imbalance (X : Finset (ℝ × ℝ)) (p q : ℝ × ℝ) : ℤ :=
  |(leftCount X p q : ℤ) - (rightCount X p q : ℤ)|

/-- Verbatim from formal-conjectures `9097e2f`, `Green75.green_75`. -/
def Green75Statement : Prop :=
    ∀ X : Finset (ℝ × ℝ), 2 ≤ #X → ∃ p ∈ X, ∃ q ∈ X, p ≠ q ∧ imbalance X p q ≤ 100

/-- Verbatim from formal-conjectures `9097e2f`, `Green75.green_75.variants.exists_constant`. -/
def Green75ExistsConstant : Prop :=
    ∃ C : ℕ, ∀ X : Finset (ℝ × ℝ), 2 ≤ #X →
      ∃ p ∈ X, ∃ q ∈ X, p ≠ q ∧ imbalance X p q ≤ C

/-- **Green 75 ⇒ Green 75 with some constant** (take `C = 100`). -/
theorem green75ExistsConstant_of_green75 (h : Green75Statement) : Green75ExistsConstant :=
  ⟨100, fun X hX => by simpa using h X hX⟩

end Implications.Combinatorics.Green75
