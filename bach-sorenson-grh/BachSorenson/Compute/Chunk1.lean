import BachSorensonCheck

/-! Chunk 1 of the finite computation: `q ∈ [2048, 4096)`.

Evaluated by `native_decide` (one auxiliary axiom
`BachSorenson.chunk_ok_1._native.native_decide.ax_*` trusting the compiled evaluation of the
core-Lean checker in `BachSorensonCheck.lean`). -/

namespace BachSorenson

theorem chunk_ok_1 : Checker.checkRange 8000000 (1 * 2048) 2048 = true := by
  native_decide

end BachSorenson
