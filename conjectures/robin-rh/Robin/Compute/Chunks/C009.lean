import RobinCompute.Data

namespace RobinCompute

/-- Chunk 9 of the verified computation (`native_decide`). -/
theorem chunk_9 : runChunk Gc s9 171798691840 = s10 := by native_decide

end RobinCompute
