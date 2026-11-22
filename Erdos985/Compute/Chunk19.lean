import Erdos985.Compute.Checker

namespace Erdos985.Compute

/-- Chunk 19 of the verified computation: `okN n` holds for all
`n ∈ [19 * 5000000, (19 + 1) * 5000000)`.

This is evaluated by `native_decide`, so it relies on an extra trust assumption: in this
Lean version `native_decide` adds an auxiliary axiom (`chunk_ok_N._native.native_decide.ax_*`,
the successor of `Lean.ofReduceBool`) asserting that the compiled evaluation is correct.
The checker itself and its soundness are proved in `Erdos985.Compute.Checker` without
such assumptions. -/
theorem chunk_ok_19 : checkFrom (19 * 5000000) 5000000 = true := by
  native_decide

end Erdos985.Compute
