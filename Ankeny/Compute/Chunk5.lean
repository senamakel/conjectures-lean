import AnkenyCheck

/-! Chunk 5 of the finite computation: `q ∈ [5 · 2^14, (5 + 1) · 2^14)`.

Evaluated by `native_decide` (one auxiliary axiom `Ankeny.chunk_ok_5._native.native_decide.ax_*`
trusting the compiled evaluation of the core-Lean checker in `AnkenyCheck.lean`). -/

namespace Ankeny

theorem chunk_ok_5 : Checker.checkRange 21 5 (5 * 16384) 16384 = true := by
  native_decide

end Ankeny
