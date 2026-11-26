import RobinCompute.Data

namespace RobinCompute

/-- Chunk 63 of the verified computation (`native_decide`). -/
theorem chunk_63 : runChunk Gc s63 1099511627776 = s64 := by native_decide

end RobinCompute
