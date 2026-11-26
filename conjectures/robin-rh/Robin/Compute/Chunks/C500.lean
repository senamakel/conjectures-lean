import RobinCompute.Data

namespace RobinCompute

/-- Chunk 500 of the verified computation (`native_decide`). -/
theorem chunk_500 : runChunk Gc s500 8607114461184 = s501 := by native_decide

end RobinCompute
