import RobinCompute.Data

namespace RobinCompute

/-- Chunk 127 of the verified computation (`native_decide`). -/
theorem chunk_127 : runChunk Gc s127 2199023255552 = s128 := by native_decide

end RobinCompute
