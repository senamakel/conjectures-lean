import BachSorensonCheck2

/-! Chunk 4 of the finite computation for the constant `2`: `q ∈ [8192, 10240)`.

Evaluated by `native_decide` (one auxiliary axiom
`BachSorenson.chunk2_ok_4._native.native_decide.ax_*` trusting the compiled evaluation of the
core-Lean checker in `BachSorensonCheck2.lean`). -/

namespace BachSorenson

theorem chunk2_ok_4 : Checker.checkRange2 8000000 (4 * 2048) 2048 = true := by
  native_decide

end BachSorenson
