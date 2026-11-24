import RobinCompute.Data

namespace RobinCompute

/-- Chunk 1 of the verified computation (`native_decide`). -/
theorem chunk_1 : runChunk Gc s1 34359738368 = s2 := by native_decide

end RobinCompute
