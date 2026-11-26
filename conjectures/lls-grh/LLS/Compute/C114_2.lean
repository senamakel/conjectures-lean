import AnkenyCheck

/-! Chunk 2 of the finite computation for `c = 11/4`: `q ∈ [2 · 2^14, (2 + 1) · 2^14)`.

Evaluated by `native_decide` (one auxiliary axiom trusting the compiled evaluation of
ankeny-grh's core-Lean checker `AnkenyCheck`). -/

namespace LLS

theorem chunk114_ok_2 : Ankeny.Checker.checkRange 11 4 32768 16384 = true := by
  native_decide

end LLS
