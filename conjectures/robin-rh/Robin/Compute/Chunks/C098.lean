import RobinCompute.Data

namespace RobinCompute

/-- Chunk 98 of the verified computation (`native_decide`). -/
theorem chunk_98 : runChunk Gc s98 1700807049216 = s99 := by native_decide

end RobinCompute
