import RobinCompute.Data

namespace RobinCompute

/-- Chunk 85 of the verified computation (`native_decide`). -/
theorem chunk_85 : runChunk Gc s85 1477468749824 = s86 := by native_decide

end RobinCompute
