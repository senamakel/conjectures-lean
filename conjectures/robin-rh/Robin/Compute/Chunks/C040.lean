import RobinCompute.Data

namespace RobinCompute

/-- Chunk 40 of the verified computation (`native_decide`). -/
theorem chunk_40 : runChunk Gc s40 704374636544 = s41 := by native_decide

end RobinCompute
