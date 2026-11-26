import BachSorensonCheck

/-! Chunk 5 of the finite computation: `q ∈ [10240, 12288)`.

Evaluated by `native_decide` (one auxiliary axiom
`BachSorenson.chunk_ok_5._native.native_decide.ax_*` trusting the compiled evaluation of the
core-Lean checker in `BachSorensonCheck.lean`). -/

namespace BachSorenson

theorem chunk_ok_5 : Checker.checkRange 8000000 (5 * 2048) 2048 = true := by
  native_decide

end BachSorenson
