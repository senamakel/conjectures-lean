import SunA243164.Compute.Checker

namespace SunA243164.Compute

/-- Chunk 14 of the finite range: the primes in `[14 * 5000000, 15 * 5000000)`, starting from
the count `π(14 * 5000000 - 1) = 4118064`.

Evaluated by `native_decide` (trust assumption `chunk_ok_14._native.native_decide.ax_*`); the
checker's soundness is `SunA243164.Compute.countFrom_sound`, proved without it. -/
theorem chunk_ok_14 : countFrom (14 * 5000000) 5000000 4118064 = some 4394304 := by
  native_decide

end SunA243164.Compute
