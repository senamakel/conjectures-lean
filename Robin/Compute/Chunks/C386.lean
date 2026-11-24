import RobinCompute.Data

namespace RobinCompute

/-- Chunk 386 of the verified computation (`native_decide`). -/
theorem chunk_386 : runChunk Gc s386 6648609374208 = s387 := by native_decide

end RobinCompute
