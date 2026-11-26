import RobinCompute.Data

namespace RobinCompute

/-- Chunk 21 of the verified computation (`native_decide`). -/
theorem chunk_21 : runChunk Gc s21 377957122048 = s22 := by native_decide

end RobinCompute
