import RobinCompute.Data

namespace RobinCompute

/-- Chunk 201 of the verified computation (`native_decide`). -/
theorem chunk_201 : runChunk Gc s201 3470333575168 = s202 := by native_decide

end RobinCompute
