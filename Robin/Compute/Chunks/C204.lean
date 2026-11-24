import RobinCompute.Data

namespace RobinCompute

/-- Chunk 204 of the verified computation (`native_decide`). -/
theorem chunk_204 : runChunk Gc s204 3521873182720 = s205 := by native_decide

end RobinCompute
