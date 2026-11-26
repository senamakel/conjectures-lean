import RobinCompute.Data

namespace RobinCompute

/-- Chunk 250 of the verified computation (`native_decide`). -/
theorem chunk_250 : runChunk Gc s250 4312147165184 = s251 := by native_decide

end RobinCompute
