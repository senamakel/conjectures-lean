import RobinCompute.Data

namespace RobinCompute

/-- Chunk 300 of the verified computation (`native_decide`). -/
theorem chunk_300 : runChunk Gc s300 5171140624384 = s301 := by native_decide

end RobinCompute
