import AnkenyCheck

/-! Chunk 7 of the finite computation: `q ∈ [7 · 2^14, (7 + 1) · 2^14)`.

Evaluated by `native_decide` (one auxiliary axiom `Ankeny.chunk_ok_7._native.native_decide.ax_*`
trusting the compiled evaluation of the core-Lean checker in `AnkenyCheck.lean`). -/

namespace Ankeny

theorem chunk_ok_7 : Checker.checkRange 21 5 (7 * 16384) 16384 = true := by
  native_decide

end Ankeny
