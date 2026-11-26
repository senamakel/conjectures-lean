import BachSorensonCheck

/-! Chunk 2 of the finite computation: `q ∈ [4096, 6144)`.

Evaluated by `native_decide` (one auxiliary axiom
`BachSorenson.chunk_ok_2._native.native_decide.ax_*` trusting the compiled evaluation of the
core-Lean checker in `BachSorensonCheck.lean`). -/

namespace BachSorenson

theorem chunk_ok_2 : Checker.checkRange 8000000 (2 * 2048) 2048 = true := by
  native_decide

end BachSorenson
