import Schoenfeld.PsiCert.Data

/-! Chunk 2 of the PsiCert run (49588 ms on the generating run). -/

namespace Schoenfeld.PsiCert

open SchoenfeldCompute

theorem chunk02 : runSegs basePrimes segsPerChunk st2 = some st3 := by native_decide

end Schoenfeld.PsiCert
