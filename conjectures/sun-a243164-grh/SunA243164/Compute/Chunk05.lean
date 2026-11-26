import SunA243164.Compute.Checker

namespace SunA243164.Compute

/-- Chunk 5 of the finite range: the primes in `[5 * 5000000, 6 * 5000000)`, starting from
the count `π(5 * 5000000 - 1) = 1565927`.

Evaluated by `native_decide` (trust assumption `chunk_ok_5._native.native_decide.ax_*`); the
checker's soundness is `SunA243164.Compute.countFrom_sound`, proved without it. -/
theorem chunk_ok_5 : countFrom (5 * 5000000) 5000000 1565927 = some 1857859 := by
  native_decide

end SunA243164.Compute
