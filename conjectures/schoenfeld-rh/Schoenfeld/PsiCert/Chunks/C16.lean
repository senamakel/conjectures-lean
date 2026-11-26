import Schoenfeld.PsiCert.Data

/-! Chunk 16 of the PsiCert run (20073 ms on the generating run). -/

namespace Schoenfeld.PsiCert

open SchoenfeldCompute

theorem chunk16 : runSegs basePrimes segsPerChunk st16 = some st17 := by native_decide

end Schoenfeld.PsiCert
