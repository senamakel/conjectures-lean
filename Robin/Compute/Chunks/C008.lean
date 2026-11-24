import RobinCompute.Data

namespace RobinCompute

/-- Chunk 8 of the verified computation (`native_decide`). -/
theorem chunk_8 : runChunk Gc s8 154618822656 = s9 := by native_decide

end RobinCompute
