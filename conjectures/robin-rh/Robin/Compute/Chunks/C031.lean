import RobinCompute.Data

namespace RobinCompute

/-- Chunk 31 of the verified computation (`native_decide`). -/
theorem chunk_31 : runChunk Gc s31 549755813888 = s32 := by native_decide

end RobinCompute
