import AnkenyCheck

/-! Chunk 11 of the finite computation for `c = 11/4`: `q ∈ [11 · 2^14, (11 + 1) · 2^14)`.

Evaluated by `native_decide` (one auxiliary axiom trusting the compiled evaluation of
ankeny-grh's core-Lean checker `AnkenyCheck`). -/

namespace LLS

theorem chunk114_ok_11 : Ankeny.Checker.checkRange 11 4 180224 16384 = true := by
  native_decide

end LLS
