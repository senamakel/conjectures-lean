import AnkenyCheck

/-! Chunk 4 of the finite computation for `c = 11/4`: `q ∈ [4 · 2^14, (4 + 1) · 2^14)`.

Evaluated by `native_decide` (one auxiliary axiom trusting the compiled evaluation of
ankeny-grh's core-Lean checker `AnkenyCheck`). -/

namespace LLS

theorem chunk114_ok_4 : Ankeny.Checker.checkRange 11 4 65536 16384 = true := by
  native_decide

end LLS
