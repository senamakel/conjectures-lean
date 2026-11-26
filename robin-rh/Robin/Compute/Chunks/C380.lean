import RobinCompute.Data

namespace RobinCompute

/-- Chunk 380 of the verified computation (`native_decide`). -/
theorem chunk_380 : runChunk Gc s380 6545530159104 = s381 := by native_decide

end RobinCompute
