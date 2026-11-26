import AnkenyCheck

/-! Chunk 6 of the finite computation for `c = 11/4`: `q ∈ [6 · 2^14, (6 + 1) · 2^14)`.

Evaluated by `native_decide` (one auxiliary axiom trusting the compiled evaluation of
ankeny-grh's core-Lean checker `AnkenyCheck`). -/

namespace LLS

theorem chunk114_ok_6 : Ankeny.Checker.checkRange 11 4 98304 16384 = true := by
  native_decide

end LLS
