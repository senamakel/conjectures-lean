import RobinCompute.Data

namespace RobinCompute

/-- Chunk 20 of the verified computation (`native_decide`). -/
theorem chunk_20 : runChunk Gc s20 360777252864 = s21 := by native_decide

end RobinCompute
