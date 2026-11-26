import RobinCompute.Data

namespace RobinCompute

/-- Chunk 381 of the verified computation (`native_decide`). -/
theorem chunk_381 : runChunk Gc s381 6562710028288 = s382 := by native_decide

end RobinCompute
