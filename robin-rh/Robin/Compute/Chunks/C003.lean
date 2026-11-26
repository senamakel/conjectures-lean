import RobinCompute.Data

namespace RobinCompute

/-- Chunk 3 of the verified computation (`native_decide`). -/
theorem chunk_3 : runChunk Gc s3 68719476736 = s4 := by native_decide

end RobinCompute
