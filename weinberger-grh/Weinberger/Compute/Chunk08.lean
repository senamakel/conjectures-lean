import Weinberger.Compute.Checker

namespace Weinberger.Compute

/-- Chunk 8 of the verified computation: `okN n` holds for all
`n ∈ [8 * 10000000, (8 + 1) * 10000000)`. Evaluated by `native_decide` (one auxiliary
axiom `chunk_ok_8._native.native_decide.ax_*`); the checker's soundness is proved in
`Weinberger.Compute.Checker` without it. -/
theorem chunk_ok_8 : checkFrom (8 * 10000000) 10000000 = true := by
  native_decide

end Weinberger.Compute
