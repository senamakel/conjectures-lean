import AnkenyCheck

/-! Chunk 3 of the finite computation: `q ∈ [3 · 2^14, (3 + 1) · 2^14)`.

Evaluated by `native_decide` (one auxiliary axiom `Ankeny.chunk_ok_3._native.native_decide.ax_*`
trusting the compiled evaluation of the core-Lean checker in `AnkenyCheck.lean`). -/

namespace Ankeny

theorem chunk_ok_3 : Checker.checkRange 21 5 (3 * 16384) 16384 = true := by
  native_decide

end Ankeny
