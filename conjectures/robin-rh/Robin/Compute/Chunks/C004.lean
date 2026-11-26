import RobinCompute.Data

namespace RobinCompute

/-- Chunk 4 of the verified computation (`native_decide`). -/
theorem chunk_4 : runChunk Gc s4 85899345920 = s5 := by native_decide

end RobinCompute
