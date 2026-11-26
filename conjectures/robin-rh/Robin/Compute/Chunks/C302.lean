import RobinCompute.Data

namespace RobinCompute

/-- Chunk 302 of the verified computation (`native_decide`). -/
theorem chunk_302 : runChunk Gc s302 5205500362752 = s303 := by native_decide

end RobinCompute
