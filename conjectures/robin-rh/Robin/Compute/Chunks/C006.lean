import RobinCompute.Data

namespace RobinCompute

/-- Chunk 6 of the verified computation (`native_decide`). -/
theorem chunk_6 : runChunk Gc s6 120259084288 = s7 := by native_decide

end RobinCompute
