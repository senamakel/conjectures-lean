import RobinCompute.Data

namespace RobinCompute

/-- Chunk 24 of the verified computation (`native_decide`). -/
theorem chunk_24 : runChunk Gc s24 429496729600 = s25 := by native_decide

end RobinCompute
