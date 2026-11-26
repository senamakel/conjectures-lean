import SunA243164.Compute.Checker

namespace SunA243164.Compute

/-- Chunk 4 of the finite range: the primes in `[4 * 5000000, 5 * 5000000)`, starting from
the count `π(4 * 5000000 - 1) = 1270607`.

Evaluated by `native_decide` (trust assumption `chunk_ok_4._native.native_decide.ax_*`); the
checker's soundness is `SunA243164.Compute.countFrom_sound`, proved without it. -/
theorem chunk_ok_4 : countFrom (4 * 5000000) 5000000 1270607 = some 1565927 := by
  native_decide

end SunA243164.Compute
