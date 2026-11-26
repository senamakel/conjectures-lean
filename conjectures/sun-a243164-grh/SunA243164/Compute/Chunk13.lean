import SunA243164.Compute.Checker

namespace SunA243164.Compute

/-- Chunk 13 of the finite range: the primes in `[13 * 5000000, 14 * 5000000)`, starting from
the count `π(13 * 5000000 - 1) = 3840554`.

Evaluated by `native_decide` (trust assumption `chunk_ok_13._native.native_decide.ax_*`); the
checker's soundness is `SunA243164.Compute.countFrom_sound`, proved without it. -/
theorem chunk_ok_13 : countFrom (13 * 5000000) 5000000 3840554 = some 4118064 := by
  native_decide

end SunA243164.Compute
