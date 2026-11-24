import Weinberger.ClassNumber.Checker

namespace Weinberger.ClassNumber

/-- Chunk 7 of the class-number computation: `okB n` holds for all
`n ∈ [7 * 10000000, (7 + 1) * 10000000)`. Evaluated by `native_decide` (one auxiliary
axiom); the checker's soundness is proved in `Weinberger.ClassNumber.Checker`. -/
theorem chunkB_ok_7 : checkFromB (7 * 10000000) 10000000 = true := by
  native_decide

end Weinberger.ClassNumber
