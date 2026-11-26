import AnkenyCheck

/-! Chunk 5 of the finite computation for `c = 11/4`: `q ∈ [5 · 2^14, (5 + 1) · 2^14)`.

Evaluated by `native_decide` (one auxiliary axiom trusting the compiled evaluation of
ankeny-grh's core-Lean checker `AnkenyCheck`). -/

namespace LLS

theorem chunk114_ok_5 : Ankeny.Checker.checkRange 11 4 81920 16384 = true := by
  native_decide

end LLS
