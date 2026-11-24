import Schoenfeld.PsiCert.Data

/-! Chunk 0 of the PsiCert run (156921 ms on the generating run). -/

namespace Schoenfeld.PsiCert

open SchoenfeldCompute

theorem chunk00 : runSegs basePrimes segsPerChunk st0 = some st1 := by native_decide

end Schoenfeld.PsiCert
