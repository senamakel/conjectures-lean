import Schoenfeld.PsiCert.Data

/-! Chunk 19 of the PsiCert run (28050 ms on the generating run). -/

namespace Schoenfeld.PsiCert

open SchoenfeldCompute

theorem chunk19 : runSegs basePrimes segsPerChunk st19 = some st20 := by native_decide

end Schoenfeld.PsiCert
