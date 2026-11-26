import RobinCompute.Data

namespace RobinCompute

/-- Chunk 16 of the verified computation (`native_decide`). -/
theorem chunk_16 : runChunk Gc s16 292057776128 = s17 := by native_decide

end RobinCompute
