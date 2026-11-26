import AnkenyCheck

/-! Chunk 3 of the finite computation for `c = 11/4`: `q ∈ [3 · 2^14, (3 + 1) · 2^14)`.

Evaluated by `native_decide` (one auxiliary axiom trusting the compiled evaluation of
ankeny-grh's core-Lean checker `AnkenyCheck`). -/

namespace LLS

theorem chunk114_ok_3 : Ankeny.Checker.checkRange 11 4 49152 16384 = true := by
  native_decide

end LLS
