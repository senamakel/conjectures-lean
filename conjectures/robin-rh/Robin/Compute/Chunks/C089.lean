import RobinCompute.Data

namespace RobinCompute

/-- Chunk 89 of the verified computation (`native_decide`). -/
theorem chunk_89 : runChunk Gc s89 1546188226560 = s90 := by native_decide

end RobinCompute
