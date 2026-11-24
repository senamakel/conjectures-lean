import Schoenfeld.PsiCert.Data

/-! Chunk 11 of the PsiCert run (30008 ms on the generating run). -/

namespace Schoenfeld.PsiCert

open SchoenfeldCompute

theorem chunk11 : runSegs basePrimes segsPerChunk st11 = some st12 := by native_decide

end Schoenfeld.PsiCert
