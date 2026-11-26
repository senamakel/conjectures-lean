import Schoenfeld.PsiCert.Data

/-! Chunk 5 of the PsiCert run (41289 ms on the generating run). -/

namespace Schoenfeld.PsiCert

open SchoenfeldCompute

theorem chunk05 : runSegs basePrimes segsPerChunk st5 = some st6 := by native_decide

end Schoenfeld.PsiCert
