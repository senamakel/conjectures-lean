import RobinCompute.Data

namespace RobinCompute

/-- Chunk 96 of the verified computation (`native_decide`). -/
theorem chunk_96 : runChunk Gc s96 1666447310848 = s97 := by native_decide

end RobinCompute
