import AnkenyCheck

/-! Chunk 0 of the finite computation for `c = 11/4`: `q ∈ [4, 2^14)` (`q = 3` is done by hand).

Evaluated by `native_decide` (one auxiliary axiom trusting the compiled evaluation of
ankeny-grh's core-Lean checker `AnkenyCheck`). -/

namespace LLS

theorem chunk114_ok_0 : Ankeny.Checker.checkRange 11 4 4 16380 = true := by
  native_decide

end LLS
