import RobinCompute.Data

namespace RobinCompute

/-- Chunk 420 of the verified computation (`native_decide`). -/
theorem chunk_420 : runChunk Gc s420 7232724926464 = s421 := by native_decide

end RobinCompute
