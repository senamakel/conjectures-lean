import AnkenyCheck

/-! Chunk 2 of the finite computation: `q ∈ [2 · 2^14, (2 + 1) · 2^14)`.

Evaluated by `native_decide` (one auxiliary axiom `Ankeny.chunk_ok_2._native.native_decide.ax_*`
trusting the compiled evaluation of the core-Lean checker in `AnkenyCheck.lean`). -/

namespace Ankeny

theorem chunk_ok_2 : Checker.checkRange 21 5 (2 * 16384) 16384 = true := by
  native_decide

end Ankeny
