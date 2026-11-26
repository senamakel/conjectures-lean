import BachSorensonCheck2

/-! Chunk 7 of the finite computation for the constant `2`: `q ∈ [14336, 16384)`.

Evaluated by `native_decide` (one auxiliary axiom
`BachSorenson.chunk2_ok_7._native.native_decide.ax_*` trusting the compiled evaluation of the
core-Lean checker in `BachSorensonCheck2.lean`). -/

namespace BachSorenson

theorem chunk2_ok_7 : Checker.checkRange2 8000000 (7 * 2048) 2048 = true := by
  native_decide

end BachSorenson
