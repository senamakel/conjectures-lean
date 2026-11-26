import AnkenyCheck

/-! Chunk 15 of the finite computation for `c = 11/4`: `q ∈ [15 · 2^14, (15 + 1) · 2^14)`.

Evaluated by `native_decide` (one auxiliary axiom trusting the compiled evaluation of
ankeny-grh's core-Lean checker `AnkenyCheck`). -/

namespace LLS

theorem chunk114_ok_15 : Ankeny.Checker.checkRange 11 4 245760 16384 = true := by
  native_decide

end LLS
