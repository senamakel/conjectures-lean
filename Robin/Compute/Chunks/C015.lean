import RobinCompute.Data

namespace RobinCompute

/-- Chunk 15 of the verified computation (`native_decide`). -/
theorem chunk_15 : runChunk Gc s15 274877906944 = s16 := by native_decide

end RobinCompute
