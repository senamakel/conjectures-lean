import SunA243164.Compute.Checker

namespace SunA243164.Compute

/-- Chunk 17 of the finite range: the primes in `[17 * 5000000, 18 * 5000000)`, starting from
the count `π(17 * 5000000 - 1) = 4943731`.

Evaluated by `native_decide` (trust assumption `chunk_ok_17._native.native_decide.ax_*`); the
checker's soundness is `SunA243164.Compute.countFrom_sound`, proved without it. -/
theorem chunk_ok_17 : countFrom (17 * 5000000) 5000000 4943731 = some 5216954 := by
  native_decide

end SunA243164.Compute
