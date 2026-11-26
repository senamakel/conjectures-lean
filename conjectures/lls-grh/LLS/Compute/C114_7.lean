import AnkenyCheck

/-! Chunk 7 of the finite computation for `c = 11/4`: `q ∈ [7 · 2^14, (7 + 1) · 2^14)`.

Evaluated by `native_decide` (one auxiliary axiom trusting the compiled evaluation of
ankeny-grh's core-Lean checker `AnkenyCheck`). -/

namespace LLS

theorem chunk114_ok_7 : Ankeny.Checker.checkRange 11 4 114688 16384 = true := by
  native_decide

end LLS
