import RobinCompute.Data

namespace RobinCompute

/-- Chunk 304 of the verified computation (`native_decide`). -/
theorem chunk_304 : runChunk Gc s304 5239860101120 = s305 := by native_decide

end RobinCompute
