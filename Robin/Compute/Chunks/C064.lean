import RobinCompute.Data

namespace RobinCompute

/-- Chunk 64 of the verified computation (`native_decide`). -/
theorem chunk_64 : runChunk Gc s64 1116691496960 = s65 := by native_decide

end RobinCompute
