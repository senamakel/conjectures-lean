import BachSorensonCheck

/-! Chunk 13 of the finite computation: `q ∈ [26624, 28672)`.

Evaluated by `native_decide` (one auxiliary axiom
`BachSorenson.chunk_ok_13._native.native_decide.ax_*` trusting the compiled evaluation of the
core-Lean checker in `BachSorensonCheck.lean`). -/

namespace BachSorenson

theorem chunk_ok_13 : Checker.checkRange 8000000 (13 * 2048) 2048 = true := by
  native_decide

end BachSorenson
