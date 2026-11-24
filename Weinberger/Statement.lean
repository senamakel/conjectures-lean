import Erdos985.Statement

/-!
# Target statements

Fixed once written (conjectures tracker, rule 3). Nothing here may be edited to make a proof go
through.

* The GRH hypothesis is `Erdos985.DirichletLNonvanishingRightOfHalf`, imported from the
  erdos-985 dependency (itself copied word for word from `src/Statements.lean` of
  leanprover-community/riemann-hypothesis). It is not restated here.
* `Idoneal.IsIdoneal`, `Idoneal.knownIdonealNumbers` and the statement
  `Idoneal.IdonealCompletenessStatement` are copied word for word from
  `FormalConjectures/Wikipedia/IdonealCompleteness.lean` of google-deepmind/formal-conjectures
  (commit `86a2f58a4d7a3a0637d15d5b2ce627592b54b956`, Apache-2.0), where the statement is the
  `sorry`-ed theorem `idoneal_numbers_completeness`.
* `ClassNumberProblem.IsClassNumberOne` and `ClassNumberProblem.StarkHeegnerStatement` are copied
  word for word from `FormalConjectures/Wikipedia/ClassNumberProblem.lean` of the same commit,
  where the statement is the `sorry`-ed theorem `class_number_problem.variants.imaginary`.
-/

namespace Idoneal

/--
Equivalent definition: A positive integer $n$ is idoneal if and only if it cannot be written as
$ab + bc + ac$ for distinct positive integers $a, b,$ and $c$.
-/
def IsIdoneal (n : ℕ) : Prop :=
  0 < n ∧
    ¬ ∃ a b c : ℕ,
      0 < a ∧ a < b ∧ b < c ∧ n = a * b + b * c + a * c

/--
The 65 known idoneal numbers that are conjectured to be the only idoneal numbers.
-/
def knownIdonealNumbers : Finset ℕ :=
  {1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 13, 15, 16, 18, 21, 22, 24, 25, 28,
   30, 33, 37, 40, 42, 45, 48, 57, 58, 60, 70, 72, 78, 85, 88, 93, 102, 105,
   112, 120, 130, 133, 165, 168, 177, 190, 210, 232, 240, 253, 273, 280, 312,
   330, 345, 357, 385, 408, 462, 520, 760, 840, 1320, 1365, 1848}

/--
Idoneal numbers completeness conjecture (the statement of `idoneal_numbers_completeness`).
-/
def IdonealCompletenessStatement : Prop :=
    ∀ n : ℕ, IsIdoneal n → n ∈ knownIdonealNumbers

end Idoneal

open Polynomial
namespace ClassNumberProblem

def IsClassNumberOne (d : ℤ) : Prop :=
  ∃ (h₂ : Irreducible (X ^ 2 - C (d : ℚ))),
  have := Fact.mk h₂
  NumberField.classNumber (AdjoinRoot (X ^ 2 - C (d : ℚ))) = 1

/--
**Stark–Heegner theorem** : For any squarefree integer `d < 0`, the class number of the imaginary
quadratic field Q(√d) is one if and only if `d ∈ {-1, -2, -3, -7, -11, -19, -43, -67, -163}`
(the statement of `class_number_problem.variants.imaginary`).
-/
def StarkHeegnerStatement : Prop :=
    { d : ℤ | Squarefree d ∧ d < 0 ∧ IsClassNumberOne d } =
    {-1, -2, -3, -7, -11, -19, -43, -67, -163}

end ClassNumberProblem
