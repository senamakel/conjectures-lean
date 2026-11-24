import Schoenfeld.PsiCert.Data

/-! Chunk 14 of the PsiCert run (21778 ms on the generating run). -/

namespace Schoenfeld.PsiCert

open SchoenfeldCompute

theorem chunk14 : runSegs basePrimes segsPerChunk st14 = some st15 := by native_decide

end Schoenfeld.PsiCert
