import Mathlib

/-!
Target statements for this project. Fixed once written (see the conjectures tracker, rule 3).

Copied verbatim from google-deepmind/formal-conjectures,
`FormalConjectures/Wikipedia/Mills.lean` (commit 86a2f58a4d7a3a0637d15d5b2ce627592b54b956):
https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/Wikipedia/Mills.lean
-/

namespace Mills

/--
Given any real $A$, `IsMills A` encodes the statement that $\lfloor A^{3^n}\rfloor,n > 0$ is prime.
-/
abbrev IsMills (A : ℝ) : Prop := ∀ (n : ℕ+), Prime ⌊A ^ (3 ^ (n : ℕ))⌋₊

/--
For a real $A$, `IsMinMills A` is the smallest value satisfying `IsMills A`.
-/
abbrev IsMinMills (A : ℝ) : Prop := IsLeast {x | x > 1 ∧ IsMills x} A

/-- The formal-conjectures statement `Mills.lower_bound_of_RH`, as a proposition:
**Mills' constant lower bound** (Caldwell–Cheng, 2005): assuming the Riemann hypothesis,
Mills' constant begins at $1.3063778838\ldots$. -/
def LowerBoundOfRH : Prop :=
  RiemannHypothesis → ∀ {A}, IsMinMills A → A ∈ Set.Ioo (1.3063778838 : ℝ) 1.3063778839

end Mills
