import RobinCompute.Data

namespace RobinCompute

/-- Chunk 402 of the verified computation (`native_decide`). -/
theorem chunk_402 : runChunk Gc s402 6923487281152 = s403 := by native_decide

end RobinCompute
