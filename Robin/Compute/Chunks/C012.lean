import RobinCompute.Data

namespace RobinCompute

/-- Chunk 12 of the verified computation (`native_decide`). -/
theorem chunk_12 : runChunk Gc s12 223338299392 = s13 := by native_decide

end RobinCompute
