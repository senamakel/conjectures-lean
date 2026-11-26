import AnkenyCheck

/-! Chunk 1 of the finite computation: `q ∈ [1 · 2^14, (1 + 1) · 2^14)`.

Evaluated by `native_decide` (one auxiliary axiom `Ankeny.chunk_ok_1._native.native_decide.ax_*`
trusting the compiled evaluation of the core-Lean checker in `AnkenyCheck.lean`). -/

namespace Ankeny

theorem chunk_ok_1 : Checker.checkRange 21 5 (1 * 16384) 16384 = true := by
  native_decide

end Ankeny
