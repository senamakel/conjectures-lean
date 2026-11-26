import RobinCompute.Data

namespace RobinCompute

/-- Chunk 365 of the verified computation (`native_decide`). -/
theorem chunk_365 : runChunk Gc s365 6287832121344 = s366 := by native_decide

end RobinCompute
