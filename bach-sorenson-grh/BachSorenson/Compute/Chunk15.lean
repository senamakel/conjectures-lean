import BachSorensonCheck

/-! Chunk 15 of the finite computation: `q ∈ [30720, 32768)`.

Evaluated by `native_decide` (one auxiliary axiom
`BachSorenson.chunk_ok_15._native.native_decide.ax_*` trusting the compiled evaluation of the
core-Lean checker in `BachSorensonCheck.lean`). -/

namespace BachSorenson

theorem chunk_ok_15 : Checker.checkRange 8000000 (15 * 2048) 2048 = true := by
  native_decide

end BachSorenson
