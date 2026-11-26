import RobinCompute.Data

namespace RobinCompute

/-- Chunk 0 of the verified computation (`native_decide`). -/
theorem chunk_0 : runChunk Gc s0 17179869184 = s1 := by native_decide

end RobinCompute
