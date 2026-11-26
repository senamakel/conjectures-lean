import BachSorensonCheck

/-! Chunk 8 of the finite computation: `q ∈ [16384, 18432)`.

Evaluated by `native_decide` (one auxiliary axiom
`BachSorenson.chunk_ok_8._native.native_decide.ax_*` trusting the compiled evaluation of the
core-Lean checker in `BachSorensonCheck.lean`). -/

namespace BachSorenson

theorem chunk_ok_8 : Checker.checkRange 8000000 (8 * 2048) 2048 = true := by
  native_decide

end BachSorenson
