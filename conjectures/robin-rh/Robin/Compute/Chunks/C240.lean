import RobinCompute.Data

namespace RobinCompute

/-- Chunk 240 of the verified computation (`native_decide`). -/
theorem chunk_240 : runChunk Gc s240 4140348473344 = s241 := by native_decide

end RobinCompute
