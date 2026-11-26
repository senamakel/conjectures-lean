import PrimitiveRootSq.Compute.Checker

namespace PrimitiveRootSq.Compute

/-- Chunk 19 of the verified computation: `okN n` holds for all
`n ∈ [19 * 5000000, (19 + 1) * 5000000)`. Evaluated by `native_decide`, which adds the
auxiliary axiom `chunk_ok_19._native.native_decide.ax_*` (the compiled evaluation agrees with
the kernel definition). The checker's soundness is `PrimitiveRootSq.Compute.checkAll_sound`. -/
theorem chunk_ok_19 : checkFrom (19 * 5000000) 5000000 = true := by
  native_decide

end PrimitiveRootSq.Compute
