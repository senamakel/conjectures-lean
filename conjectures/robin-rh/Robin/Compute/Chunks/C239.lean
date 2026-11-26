import RobinCompute.Data

namespace RobinCompute

/-- Chunk 239 of the verified computation (`native_decide`). -/
theorem chunk_239 : runChunk Gc s239 4123168604160 = s240 := by native_decide

end RobinCompute
