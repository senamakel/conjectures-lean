import RobinCompute.Data

namespace RobinCompute

/-- Chunk 499 of the verified computation (`native_decide`). -/
theorem chunk_499 : runChunk Gc s499 8589934592000 = s500 := by native_decide

end RobinCompute
