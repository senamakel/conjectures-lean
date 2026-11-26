import BachSorensonCheck

/-! Chunk 3 of the finite computation: `q ∈ [6144, 8192)`.

Evaluated by `native_decide` (one auxiliary axiom
`BachSorenson.chunk_ok_3._native.native_decide.ax_*` trusting the compiled evaluation of the
core-Lean checker in `BachSorensonCheck.lean`). -/

namespace BachSorenson

theorem chunk_ok_3 : Checker.checkRange 8000000 (3 * 2048) 2048 = true := by
  native_decide

end BachSorenson
