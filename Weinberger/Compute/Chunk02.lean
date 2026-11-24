import Weinberger.Compute.Checker

namespace Weinberger.Compute

/-- Chunk 2 of the verified computation: `okN n` holds for all
`n ∈ [2 * 10000000, (2 + 1) * 10000000)`. Evaluated by `native_decide` (one auxiliary
axiom `chunk_ok_2._native.native_decide.ax_*`); the checker's soundness is proved in
`Weinberger.Compute.Checker` without it. -/
theorem chunk_ok_2 : checkFrom (2 * 10000000) 10000000 = true := by
  native_decide

end Weinberger.Compute
