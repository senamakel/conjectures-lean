import Weinberger.Compute.Checker

namespace Weinberger.Compute

/-- Chunk 3 of the verified computation: `okN n` holds for all
`n ∈ [3 * 10000000, (3 + 1) * 10000000)`. Evaluated by `native_decide` (one auxiliary
axiom `chunk_ok_3._native.native_decide.ax_*`); the checker's soundness is proved in
`Weinberger.Compute.Checker` without it. -/
theorem chunk_ok_3 : checkFrom (3 * 10000000) 10000000 = true := by
  native_decide

end Weinberger.Compute
