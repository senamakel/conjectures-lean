import RobinCompute.Data

namespace RobinCompute

/-- Chunk 400 of the verified computation (`native_decide`). -/
theorem chunk_400 : runChunk Gc s400 6889127542784 = s401 := by native_decide

end RobinCompute
