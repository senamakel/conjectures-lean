import RobinCompute.Data

namespace RobinCompute

/-- Chunk 123 of the verified computation (`native_decide`). -/
theorem chunk_123 : runChunk Gc s123 2130303778816 = s124 := by native_decide

end RobinCompute
