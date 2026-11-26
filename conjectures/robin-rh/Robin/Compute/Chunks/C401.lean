import RobinCompute.Data

namespace RobinCompute

/-- Chunk 401 of the verified computation (`native_decide`). -/
theorem chunk_401 : runChunk Gc s401 6906307411968 = s402 := by native_decide

end RobinCompute
