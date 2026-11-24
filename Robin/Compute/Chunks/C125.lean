import RobinCompute.Data

namespace RobinCompute

/-- Chunk 125 of the verified computation (`native_decide`). -/
theorem chunk_125 : runChunk Gc s125 2164663517184 = s126 := by native_decide

end RobinCompute
