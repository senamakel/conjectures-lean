import Schoenfeld.PsiCert.Data

/-! Chunk 17 of the PsiCert run (26484 ms on the generating run). -/

namespace Schoenfeld.PsiCert

open SchoenfeldCompute

theorem chunk17 : runSegs basePrimes segsPerChunk st17 = some st18 := by native_decide

end Schoenfeld.PsiCert
