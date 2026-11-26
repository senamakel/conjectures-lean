import RobinCompute.Data

namespace RobinCompute

/-- Chunk 600 of the verified computation (`native_decide`). -/
theorem chunk_600 : runChunk Gc s600 10325101379584 = s601 := by native_decide

end RobinCompute
