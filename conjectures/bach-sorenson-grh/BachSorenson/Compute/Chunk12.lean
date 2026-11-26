import BachSorensonCheck

/-! Chunk 12 of the finite computation: `q ∈ [24576, 26624)`.

Evaluated by `native_decide` (one auxiliary axiom
`BachSorenson.chunk_ok_12._native.native_decide.ax_*` trusting the compiled evaluation of the
core-Lean checker in `BachSorensonCheck.lean`). -/

namespace BachSorenson

theorem chunk_ok_12 : Checker.checkRange 8000000 (12 * 2048) 2048 = true := by
  native_decide

end BachSorenson
