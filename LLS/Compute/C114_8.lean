import AnkenyCheck

/-! Chunk 8 of the finite computation for `c = 11/4`: `q ∈ [8 · 2^14, (8 + 1) · 2^14)`.

Evaluated by `native_decide` (one auxiliary axiom trusting the compiled evaluation of
ankeny-grh's core-Lean checker `AnkenyCheck`). -/

namespace LLS

theorem chunk114_ok_8 : Ankeny.Checker.checkRange 11 4 131072 16384 = true := by
  native_decide

end LLS
