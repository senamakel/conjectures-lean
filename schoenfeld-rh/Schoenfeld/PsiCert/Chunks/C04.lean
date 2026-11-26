import Schoenfeld.PsiCert.Data

/-! Chunk 4 of the PsiCert run (41715 ms on the generating run). -/

namespace Schoenfeld.PsiCert

open SchoenfeldCompute

theorem chunk04 : runSegs basePrimes segsPerChunk st4 = some st5 := by native_decide

end Schoenfeld.PsiCert
