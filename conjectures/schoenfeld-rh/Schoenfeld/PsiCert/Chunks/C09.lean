import Schoenfeld.PsiCert.Data

/-! Chunk 9 of the PsiCert run (29883 ms on the generating run). -/

namespace Schoenfeld.PsiCert

open SchoenfeldCompute

theorem chunk09 : runSegs basePrimes segsPerChunk st9 = some st10 := by native_decide

end Schoenfeld.PsiCert
