import RobinCompute.Data

namespace RobinCompute

/-- Chunk 5 of the verified computation (`native_decide`). -/
theorem chunk_5 : runChunk Gc s5 103079215104 = s6 := by native_decide

end RobinCompute
