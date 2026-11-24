import Weinberger.Compute.Checker

namespace Weinberger.Compute

/-- Chunk 1 of the verified computation: `okN n` holds for all
`n ∈ [1 * 10000000, (1 + 1) * 10000000)`. Evaluated by `native_decide` (one auxiliary
axiom `chunk_ok_1._native.native_decide.ax_*`); the checker's soundness is proved in
`Weinberger.Compute.Checker` without it. -/
theorem chunk_ok_1 : checkFrom (1 * 10000000) 10000000 = true := by
  native_decide

end Weinberger.Compute
