import RobinCompute.Data

namespace RobinCompute

/-- Chunk 350 of the verified computation (`native_decide`). -/
theorem chunk_350 : runChunk Gc s350 6030134083584 = s351 := by native_decide

end RobinCompute
