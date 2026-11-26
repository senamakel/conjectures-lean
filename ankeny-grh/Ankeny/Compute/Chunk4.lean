import AnkenyCheck

/-! Chunk 4 of the finite computation: `q ∈ [4 · 2^14, (4 + 1) · 2^14)`.

Evaluated by `native_decide` (one auxiliary axiom `Ankeny.chunk_ok_4._native.native_decide.ax_*`
trusting the compiled evaluation of the core-Lean checker in `AnkenyCheck.lean`). -/

namespace Ankeny

theorem chunk_ok_4 : Checker.checkRange 21 5 (4 * 16384) 16384 = true := by
  native_decide

end Ankeny
