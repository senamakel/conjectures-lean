import RobinCompute.Data

namespace RobinCompute

/-- Chunk 10 of the verified computation (`native_decide`). -/
theorem chunk_10 : runChunk Gc s10 188978561024 = s11 := by native_decide

end RobinCompute
