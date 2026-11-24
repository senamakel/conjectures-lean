import RobinCompute.Data

namespace RobinCompute

/-- Chunk 601 of the verified computation (`native_decide`). -/
theorem chunk_601 : runChunk Gc s601 10342281248768 = s602 := by native_decide

end RobinCompute
