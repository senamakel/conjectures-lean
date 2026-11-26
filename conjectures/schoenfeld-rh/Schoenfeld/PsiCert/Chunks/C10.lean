import Schoenfeld.PsiCert.Data

/-! Chunk 10 of the PsiCert run (26845 ms on the generating run). -/

namespace Schoenfeld.PsiCert

open SchoenfeldCompute

theorem chunk10 : runSegs basePrimes segsPerChunk st10 = some st11 := by native_decide

end Schoenfeld.PsiCert
