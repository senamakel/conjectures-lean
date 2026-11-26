import RobinCompute.Data

namespace RobinCompute

/-- Chunk 90 of the verified computation (`native_decide`). -/
theorem chunk_90 : runChunk Gc s90 1563368095744 = s91 := by native_decide

end RobinCompute
