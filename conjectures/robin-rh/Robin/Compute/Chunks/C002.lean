import RobinCompute.Data

namespace RobinCompute

/-- Chunk 2 of the verified computation (`native_decide`). -/
theorem chunk_2 : runChunk Gc s2 51539607552 = s3 := by native_decide

end RobinCompute
