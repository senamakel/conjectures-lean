import RobinCompute.Data

namespace RobinCompute

/-- Chunk 23 of the verified computation (`native_decide`). -/
theorem chunk_23 : runChunk Gc s23 412316860416 = s24 := by native_decide

end RobinCompute
