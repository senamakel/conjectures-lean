import RobinCompute.Data

namespace RobinCompute

/-- Chunk 320 of the verified computation (`native_decide`). -/
theorem chunk_320 : runChunk Gc s320 5514738008064 = s321 := by native_decide

end RobinCompute
