import BachSorensonCheck

/-! Chunk 14 of the finite computation: `q ∈ [28672, 30720)`.

Evaluated by `native_decide` (one auxiliary axiom
`BachSorenson.chunk_ok_14._native.native_decide.ax_*` trusting the compiled evaluation of the
core-Lean checker in `BachSorensonCheck.lean`). -/

namespace BachSorenson

theorem chunk_ok_14 : Checker.checkRange 8000000 (14 * 2048) 2048 = true := by
  native_decide

end BachSorenson
