import AnkenyCheck

/-! Chunk 6 of the finite computation: `q ∈ [6 · 2^14, (6 + 1) · 2^14)`.

Evaluated by `native_decide` (one auxiliary axiom `Ankeny.chunk_ok_6._native.native_decide.ax_*`
trusting the compiled evaluation of the core-Lean checker in `AnkenyCheck.lean`). -/

namespace Ankeny

theorem chunk_ok_6 : Checker.checkRange 21 5 (6 * 16384) 16384 = true := by
  native_decide

end Ankeny
