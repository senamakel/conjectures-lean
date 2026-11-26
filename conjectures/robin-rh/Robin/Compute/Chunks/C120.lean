import RobinCompute.Data

namespace RobinCompute

/-- Chunk 120 of the verified computation (`native_decide`). -/
theorem chunk_120 : runChunk Gc s120 2078764171264 = s121 := by native_decide

end RobinCompute
