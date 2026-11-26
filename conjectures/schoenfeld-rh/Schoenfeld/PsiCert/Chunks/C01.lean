import Schoenfeld.PsiCert.Data

/-! Chunk 1 of the PsiCert run (75302 ms on the generating run). -/

namespace Schoenfeld.PsiCert

open SchoenfeldCompute

theorem chunk01 : runSegs basePrimes segsPerChunk st1 = some st2 := by native_decide

end Schoenfeld.PsiCert
