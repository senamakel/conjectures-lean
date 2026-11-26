import PrimitiveRootSq.Compute.Checker

namespace PrimitiveRootSq.Compute

/-- Chunk 13 of the verified computation: `okN n` holds for all
`n ∈ [13 * 5000000, (13 + 1) * 5000000)`. Evaluated by `native_decide`, which adds the
auxiliary axiom `chunk_ok_13._native.native_decide.ax_*` (the compiled evaluation agrees with
the kernel definition). The checker's soundness is `PrimitiveRootSq.Compute.checkAll_sound`. -/
theorem chunk_ok_13 : checkFrom (13 * 5000000) 5000000 = true := by
  native_decide

end PrimitiveRootSq.Compute
