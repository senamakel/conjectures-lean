import Schoenfeld.PsiCert.Data

/-! Chunk 13 of the PsiCert run (22597 ms on the generating run). -/

namespace Schoenfeld.PsiCert

open SchoenfeldCompute

theorem chunk13 : runSegs basePrimes segsPerChunk st13 = some st14 := by native_decide

end Schoenfeld.PsiCert
