import RobinCompute.Data

namespace RobinCompute

/-- Chunk 180 of the verified computation (`native_decide`). -/
theorem chunk_180 : runChunk Gc s180 3109556322304 = s181 := by native_decide

end RobinCompute
