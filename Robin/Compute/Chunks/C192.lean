import RobinCompute.Data

namespace RobinCompute

/-- Chunk 192 of the verified computation (`native_decide`). -/
theorem chunk_192 : runChunk Gc s192 3315714752512 = s193 := by native_decide

end RobinCompute
