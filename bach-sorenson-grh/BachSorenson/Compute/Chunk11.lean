import BachSorensonCheck

/-! Chunk 11 of the finite computation: `q ∈ [22528, 24576)`.

Evaluated by `native_decide` (one auxiliary axiom
`BachSorenson.chunk_ok_11._native.native_decide.ax_*` trusting the compiled evaluation of the
core-Lean checker in `BachSorensonCheck.lean`). -/

namespace BachSorenson

theorem chunk_ok_11 : Checker.checkRange 8000000 (11 * 2048) 2048 = true := by
  native_decide

end BachSorenson
