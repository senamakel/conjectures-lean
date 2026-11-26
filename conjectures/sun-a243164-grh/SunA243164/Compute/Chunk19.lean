import SunA243164.Compute.Checker

namespace SunA243164.Compute

/-- Chunk 19 of the finite range: the primes in `[19 * 5000000, 20 * 5000000)`, starting from
the count `π(19 * 5000000 - 1) = 5489749`.

Evaluated by `native_decide` (trust assumption `chunk_ok_19._native.native_decide.ax_*`); the
checker's soundness is `SunA243164.Compute.countFrom_sound`, proved without it. -/
theorem chunk_ok_19 : countFrom (19 * 5000000) 5000000 5489749 = some 5761455 := by
  native_decide

end SunA243164.Compute
