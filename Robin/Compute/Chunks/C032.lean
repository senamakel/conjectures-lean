import RobinCompute.Data

namespace RobinCompute

/-- Chunk 32 of the verified computation (`native_decide`). -/
theorem chunk_32 : runChunk Gc s32 566935683072 = s33 := by native_decide

end RobinCompute
