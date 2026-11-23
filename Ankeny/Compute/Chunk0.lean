import AnkenyCheck

/-! Chunk 0 of the finite computation: `q ∈ [0 · 2^14, (0 + 1) · 2^14)`.

Evaluated by `native_decide` (one auxiliary axiom `Ankeny.chunk_ok_0._native.native_decide.ax_*`
trusting the compiled evaluation of the core-Lean checker in `AnkenyCheck.lean`). -/

namespace Ankeny

theorem chunk_ok_0 : Checker.checkRange 21 5 (0 * 16384) 16384 = true := by
  native_decide

end Ankeny
