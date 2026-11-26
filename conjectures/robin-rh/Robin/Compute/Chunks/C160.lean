import RobinCompute.Data

namespace RobinCompute

/-- Chunk 160 of the verified computation (`native_decide`). -/
theorem chunk_160 : runChunk Gc s160 2765958938624 = s161 := by native_decide

end RobinCompute
