import PrimitiveRootSq.Compute.Checker

namespace PrimitiveRootSq.Compute

/-- Chunk 5 of the verified computation: `okN n` holds for all
`n ∈ [5 * 5000000, (5 + 1) * 5000000)`. Evaluated by `native_decide`, which adds the
auxiliary axiom `chunk_ok_5._native.native_decide.ax_*` (the compiled evaluation agrees with
the kernel definition). The checker's soundness is `PrimitiveRootSq.Compute.checkAll_sound`. -/
theorem chunk_ok_5 : checkFrom (5 * 5000000) 5000000 = true := by
  native_decide

end PrimitiveRootSq.Compute
