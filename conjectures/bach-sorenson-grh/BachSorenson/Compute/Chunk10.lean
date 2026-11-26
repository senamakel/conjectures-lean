import BachSorensonCheck

/-! Chunk 10 of the finite computation: `q ∈ [20480, 22528)`.

Evaluated by `native_decide` (one auxiliary axiom
`BachSorenson.chunk_ok_10._native.native_decide.ax_*` trusting the compiled evaluation of the
core-Lean checker in `BachSorensonCheck.lean`). -/

namespace BachSorenson

theorem chunk_ok_10 : Checker.checkRange 8000000 (10 * 2048) 2048 = true := by
  native_decide

end BachSorenson
