import Implications.ABC.Erdos936
import Implications.ABC.Variants

/-!
# Brocard's problem under the abc conjecture (Overholt 1993)

formal-conjectures states Brocard's problem as an exact set (`FormalConjectures/ErdosProblems/398.lean`,
commit `9097e2f`; `FormalConjectures/Wikipedia/BrocardProblem.lean` points to it):

```
theorem erdos_398 : {n | ∃ m, n ! + 1 = m ^ 2} = {4, 5, 7}
```

abc cannot decide which solutions exist. Overholt (*Bull. London Math. Soc.* 25 (1993) 104,
unverified) proved that abc implies finitely many solutions. `Erdos398.BrocardFinite` is **our
statement** of that finiteness version, with the set of `erdos_398` copied verbatim. `erdos_398`
implies it; it does not imply `erdos_398`.

Deduction: a nonzero square is powerful, so a solution `n` makes `n! + 1` powerful, and
`erdos_936_factorial_add_one_of_abc` (merged in `Implications.ABC.Erdos936`) says `n! + 1` is
powerful for only finitely many `n`.
-/

namespace Erdos398

open Nat

/-- **Our statement** (not in formal-conjectures): Brocard's equation `n! + 1 = m²` has only
finitely many solutions `n`. The finiteness weakening of `erdos_398`. -/
def BrocardFinite : Prop := {n | ∃ m, n ! + 1 = m ^ 2}.Finite

end Erdos398

namespace Implications.Abc

open _root_.ABC Erdos398 Nat

/-- abc implies Brocard's equation `n! + 1 = m²` has only finitely many solutions. -/
theorem brocardFinite_of_abc (habc : ABCConjecture) : BrocardFinite := by
  have hev := erdos_936_factorial_add_one_of_abc habc
  apply ((Nat.frequently_atTop_iff_infinite (p := fun n => ∃ m, n ! + 1 = m ^ 2)).not.1 ?_).of_not_not
  intro hfreq
  apply hfreq
  filter_upwards [hev] with n hn hsol
  obtain ⟨m, hm⟩ := hsol
  exact hn (hm ▸ powerful_sq m)

end Implications.Abc
