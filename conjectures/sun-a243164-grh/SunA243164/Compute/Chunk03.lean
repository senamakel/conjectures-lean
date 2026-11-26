import SunA243164.Compute.Checker

namespace SunA243164.Compute

/-- Chunk 3 of the finite range: the primes in `[3 * 5000000, 4 * 5000000)`, starting from
the count `π(3 * 5000000 - 1) = 970704`.

Evaluated by `native_decide` (trust assumption `chunk_ok_3._native.native_decide.ax_*`); the
checker's soundness is `SunA243164.Compute.countFrom_sound`, proved without it. -/
theorem chunk_ok_3 : countFrom (3 * 5000000) 5000000 970704 = some 1270607 := by
  native_decide

end SunA243164.Compute
