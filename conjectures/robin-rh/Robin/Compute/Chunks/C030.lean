import RobinCompute.Data

namespace RobinCompute

/-- Chunk 30 of the verified computation (`native_decide`). -/
theorem chunk_30 : runChunk Gc s30 532575944704 = s31 := by native_decide

end RobinCompute
