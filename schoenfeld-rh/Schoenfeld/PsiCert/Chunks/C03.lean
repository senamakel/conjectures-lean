import Schoenfeld.PsiCert.Data

/-! Chunk 3 of the PsiCert run (44472 ms on the generating run). -/

namespace Schoenfeld.PsiCert

open SchoenfeldCompute

theorem chunk03 : runSegs basePrimes segsPerChunk st3 = some st4 := by native_decide

end Schoenfeld.PsiCert
