import Mathlib

/-!
# Target statements for erdos-969 (fixed once written; see the conjectures tracker, rule 3)

`squarefreeCounting` and `squarefreeCountingError` are copied verbatim from
google-deepmind/formal-conjectures, `FormalConjectures/ErdosProblems/969.lean`
(commit `86a2f58a`, checked 2026-11-24). That file has no RH-conditional statement (only the open
`erdos_969` and the two `research solved` variants `E = o(√x)` and `E ≠ o(x^{1/4})`), so
`AxerBound` is fixed here.

`AxerBound`: assuming RH, `E(x) = O(x^{2/5+ε})` for every `ε > 0` (Axer 1911; Montgomery–Vaughan,
*Multiplicative Number Theory I*, Exercise 13.2.1.14). The theorem itself is stated in
`Erdos969.Main`. It is **not** Erdős Problem 969, which asks for the true order of `E` and is open
even under RH.
-/

namespace Erdos969

open Filter Asymptotics

/-- The squarefree counting function `Q(x)`. -/
def squarefreeCounting (x : ℕ) : ℕ :=
  ((Finset.Icc 1 x).filter Squarefree).card

/-- The error term in `Q(x) = (6 / π^2) x + E(x)`. -/
noncomputable def squarefreeCountingError (x : ℕ) : ℝ :=
  (squarefreeCounting x : ℝ) - 6 / Real.pi ^ 2 * x

/-- **Axer's bound**: `E(x) = O(x^{2/5+ε})` for every `ε > 0`. -/
def AxerBound : Prop :=
  ∀ ε : ℝ, 0 < ε →
    (fun x : ℕ => |squarefreeCountingError x|) =O[atTop] fun x : ℕ => (x : ℝ) ^ (2 / 5 + ε)

end Erdos969
