import RobinCompute.Data

namespace RobinCompute

/-- Chunk 60 of the verified computation (`native_decide`). -/
theorem chunk_60 : runChunk Gc s60 1047972020224 = s61 := by native_decide

end RobinCompute
