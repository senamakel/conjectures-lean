import AnkenyCheck

/-! Chunk 14 of the finite computation for `c = 11/4`: `q ∈ [14 · 2^14, (14 + 1) · 2^14)`.

Evaluated by `native_decide` (one auxiliary axiom trusting the compiled evaluation of
ankeny-grh's core-Lean checker `AnkenyCheck`). -/

namespace LLS

theorem chunk114_ok_14 : Ankeny.Checker.checkRange 11 4 229376 16384 = true := by
  native_decide

end LLS
