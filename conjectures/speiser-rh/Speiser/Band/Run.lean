import SpeiserCompute.Core

/-!
# The band computation, run by `native_decide`

Two boxes, `[0, 1/2] × [5/2, 7]` and its mirror image, each bisected (at most 40 levels) until
every piece passes `cellOK`. About 71,000 pieces each; about 3 minutes of CPU in all.
-/

namespace Speiser.Band

open SpeiserCompute

/-- The upper half of the band. -/
theorem coverOK_upper : coverOK 0 (D / 2) (5 * D / 2) (7 * D) 40 = true := by native_decide

/-- The lower half of the band. -/
theorem coverOK_lower : coverOK 0 (D / 2) (-7 * D) (-5 * D / 2) 40 = true := by native_decide

end Speiser.Band
