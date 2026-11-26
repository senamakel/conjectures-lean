import Schoenfeld.PsiCert.Data

/-! Chunk 12 of the PsiCert run (28443 ms on the generating run). -/

namespace Schoenfeld.PsiCert

open SchoenfeldCompute

theorem chunk12 : runSegs basePrimes segsPerChunk st12 = some st13 := by native_decide

end Schoenfeld.PsiCert
