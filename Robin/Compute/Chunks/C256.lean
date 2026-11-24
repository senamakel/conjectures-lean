import RobinCompute.Data

namespace RobinCompute

/-- Chunk 256 of the verified computation (`native_decide`). -/
theorem chunk_256 : runChunk Gc s256 4415226380288 = s257 := by native_decide

end RobinCompute
