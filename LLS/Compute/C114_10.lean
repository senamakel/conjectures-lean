import AnkenyCheck

/-! Chunk 10 of the finite computation for `c = 11/4`: `q ∈ [10 · 2^14, (10 + 1) · 2^14)`.

Evaluated by `native_decide` (one auxiliary axiom trusting the compiled evaluation of
ankeny-grh's core-Lean checker `AnkenyCheck`). -/

namespace LLS

theorem chunk114_ok_10 : Ankeny.Checker.checkRange 11 4 163840 16384 = true := by
  native_decide

end LLS
