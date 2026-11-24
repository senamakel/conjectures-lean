import Schoenfeld.PsiCert.Data

/-! Chunk 7 of the PsiCert run (47673 ms on the generating run). -/

namespace Schoenfeld.PsiCert

open SchoenfeldCompute

theorem chunk07 : runSegs basePrimes segsPerChunk st7 = some st8 := by native_decide

end Schoenfeld.PsiCert
