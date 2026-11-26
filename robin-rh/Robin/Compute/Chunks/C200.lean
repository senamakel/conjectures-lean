import RobinCompute.Data

namespace RobinCompute

/-- Chunk 200 of the verified computation (`native_decide`). -/
theorem chunk_200 : runChunk Gc s200 3453153705984 = s201 := by native_decide

end RobinCompute
