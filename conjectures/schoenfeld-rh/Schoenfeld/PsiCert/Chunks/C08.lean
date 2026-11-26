import Schoenfeld.PsiCert.Data

/-! Chunk 8 of the PsiCert run (41601 ms on the generating run). -/

namespace Schoenfeld.PsiCert

open SchoenfeldCompute

theorem chunk08 : runSegs basePrimes segsPerChunk st8 = some st9 := by native_decide

end Schoenfeld.PsiCert
