import AnkenyCheck

/-! Chunk 13 of the finite computation for `c = 11/4`: `q ∈ [13 · 2^14, (13 + 1) · 2^14)`.

Evaluated by `native_decide` (one auxiliary axiom trusting the compiled evaluation of
ankeny-grh's core-Lean checker `AnkenyCheck`). -/

namespace LLS

theorem chunk114_ok_13 : Ankeny.Checker.checkRange 11 4 212992 16384 = true := by
  native_decide

end LLS
