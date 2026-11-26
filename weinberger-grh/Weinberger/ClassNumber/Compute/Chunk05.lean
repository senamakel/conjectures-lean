import Weinberger.ClassNumber.Checker

namespace Weinberger.ClassNumber

/-- Chunk 5 of the class-number computation: `okB n` holds for all
`n ∈ [5 * 10000000, (5 + 1) * 10000000)`. Evaluated by `native_decide` (one auxiliary
axiom); the checker's soundness is proved in `Weinberger.ClassNumber.Checker`. -/
theorem chunkB_ok_5 : checkFromB (5 * 10000000) 10000000 = true := by
  native_decide

end Weinberger.ClassNumber
