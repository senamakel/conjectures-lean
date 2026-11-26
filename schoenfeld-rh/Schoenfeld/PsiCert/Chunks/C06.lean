import Schoenfeld.PsiCert.Data

/-! Chunk 6 of the PsiCert run (43963 ms on the generating run). -/

namespace Schoenfeld.PsiCert

open SchoenfeldCompute

theorem chunk06 : runSegs basePrimes segsPerChunk st6 = some st7 := by native_decide

end Schoenfeld.PsiCert
