import RobinCompute.Data

namespace RobinCompute

/-- Chunk 7 of the verified computation (`native_decide`). -/
theorem chunk_7 : runChunk Gc s7 137438953472 = s8 := by native_decide

end RobinCompute
