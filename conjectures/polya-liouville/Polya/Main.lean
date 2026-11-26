import Polya.Check

/-!
# Pólya's conjecture is false

`L(906150257) = 1` (Tanaka's counterexample), so `L(n) ≤ 0` fails at `n = 906150257 ≥ 2`.

One `native_decide` (`Polya.Check.liouville_906150257_check`): it fills the tables of `M` at the
`2·30102` points `y ≤ 30102` and `⌊906150257/a⌋`, checks the identity `∑_{k ≤ y} M(⌊y/k⌋) = 1` at
each of them, and sums `M(⌊906150257/d²⌋)` over `d ≤ 30102`. Soundness: `runLiouville_sound`.
-/

namespace Polya

namespace Check

/-- The table check for `L(906150257) = 1`. Uses `native_decide`. -/
theorem liouville_906150257_check : runLiouville 906150257 1 = true := by
  native_decide

end Check

/-- `L(906150257) = 1`. -/
theorem liouvilleSum_906150257 : liouvilleSum 906150257 = 1 :=
  Check.runLiouville_sound Check.liouville_906150257_check

/-- Pólya's conjecture is false. -/
theorem polya_conjecture_false : ¬ PolyaConjecture := by
  intro h
  have := h 906150257 (by norm_num)
  rw [liouvilleSum_906150257] at this
  exact absurd this (by norm_num)

end Polya
