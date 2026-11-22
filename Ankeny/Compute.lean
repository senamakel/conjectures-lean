import Ankeny.Finite

/-!
# The finite computation: `allOK (2^14) = true`

For every `q < 2^14 = 16384` with `q ≥ 3`, the units of `(ZMod q)ˣ` with residue
`≤ yOf q ≤ 5 log² q` generate the whole group. The checker `Ankeny.Checker.checkGen` and its
soundness theorem `Ankeny.Checker.closure_eq_top_of_checkGen` are proved in Lean without any
computational trust; only this evaluation uses `native_decide`.

**Trust assumption.** `native_decide` adds one auxiliary axiom
(`Ankeny.allOK_Q₀._native.native_decide.ax_*`) asserting that the compiled evaluation of
`allOK (2^14)` agrees with its kernel definition. Kernel `decide` is out of reach for this size
(about `10^8` array operations).
-/

namespace Ankeny

theorem allOK_Q₀ : allOK (2 ^ 14) = true := by
  native_decide

end Ankeny
