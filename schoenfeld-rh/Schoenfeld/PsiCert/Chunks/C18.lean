import Schoenfeld.PsiCert.Data

/-! Chunk 18 of the PsiCert run (25443 ms on the generating run). -/

namespace Schoenfeld.PsiCert

open SchoenfeldCompute

theorem chunk18 : runSegs basePrimes segsPerChunk st18 = some st19 := by native_decide

end Schoenfeld.PsiCert
