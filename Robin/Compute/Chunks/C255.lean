import RobinCompute.Data

namespace RobinCompute

/-- Chunk 255 of the verified computation (`native_decide`). -/
theorem chunk_255 : runChunk Gc s255 4398046511104 = s256 := by native_decide

end RobinCompute
