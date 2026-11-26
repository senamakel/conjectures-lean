import BachSorensonCheck

/-! Chunk 6 of the finite computation: `q ∈ [12288, 14336)`.

Evaluated by `native_decide` (one auxiliary axiom
`BachSorenson.chunk_ok_6._native.native_decide.ax_*` trusting the compiled evaluation of the
core-Lean checker in `BachSorensonCheck.lean`). -/

namespace BachSorenson

theorem chunk_ok_6 : Checker.checkRange 8000000 (6 * 2048) 2048 = true := by
  native_decide

end BachSorenson
