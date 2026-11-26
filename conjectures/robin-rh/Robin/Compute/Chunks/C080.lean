import RobinCompute.Data

namespace RobinCompute

/-- Chunk 80 of the verified computation (`native_decide`). -/
theorem chunk_80 : runChunk Gc s80 1391569403904 = s81 := by native_decide

end RobinCompute
