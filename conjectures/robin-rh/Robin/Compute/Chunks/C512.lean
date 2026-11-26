import RobinCompute.Data

namespace RobinCompute

/-- Chunk 512 of the verified computation (`native_decide`). -/
theorem chunk_512 : runChunk Gc s512 8813272891392 = s513 := by native_decide

end RobinCompute
