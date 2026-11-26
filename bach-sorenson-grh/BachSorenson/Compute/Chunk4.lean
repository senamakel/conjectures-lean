import BachSorensonCheck

/-! Chunk 4 of the finite computation: `q ∈ [8192, 10240)`.

Evaluated by `native_decide` (one auxiliary axiom
`BachSorenson.chunk_ok_4._native.native_decide.ax_*` trusting the compiled evaluation of the
core-Lean checker in `BachSorensonCheck.lean`). -/

namespace BachSorenson

theorem chunk_ok_4 : Checker.checkRange 8000000 (4 * 2048) 2048 = true := by
  native_decide

end BachSorenson
