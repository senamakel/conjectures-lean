import RobinCompute.Data

namespace RobinCompute

/-- Chunk 128 of the verified computation (`native_decide`). -/
theorem chunk_128 : runChunk Gc s128 2216203124736 = s129 := by native_decide

end RobinCompute
