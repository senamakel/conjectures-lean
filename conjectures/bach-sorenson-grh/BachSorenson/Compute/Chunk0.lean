import BachSorensonCheck

/-! Chunk 0 of the finite computation: `q ∈ [0, 2048)`.

Evaluated by `native_decide` (one auxiliary axiom
`BachSorenson.chunk_ok_0._native.native_decide.ax_*` trusting the compiled evaluation of the
core-Lean checker in `BachSorensonCheck.lean`). -/

namespace BachSorenson

theorem chunk_ok_0 : Checker.checkRange 8000000 (0 * 2048) 2048 = true := by
  native_decide

end BachSorenson
