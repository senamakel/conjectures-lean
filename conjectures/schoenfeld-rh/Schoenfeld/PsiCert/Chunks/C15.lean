import Schoenfeld.PsiCert.Data

/-! Chunk 15 of the PsiCert run (23129 ms on the generating run). -/

namespace Schoenfeld.PsiCert

open SchoenfeldCompute

theorem chunk15 : runSegs basePrimes segsPerChunk st15 = some st16 := by native_decide

end Schoenfeld.PsiCert
