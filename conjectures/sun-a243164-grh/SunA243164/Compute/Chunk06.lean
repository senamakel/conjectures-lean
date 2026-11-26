import SunA243164.Compute.Checker

namespace SunA243164.Compute

/-- Chunk 6 of the finite range: the primes in `[6 * 5000000, 7 * 5000000)`, starting from
the count `π(6 * 5000000 - 1) = 1857859`.

Evaluated by `native_decide` (trust assumption `chunk_ok_6._native.native_decide.ax_*`); the
checker's soundness is `SunA243164.Compute.countFrom_sound`, proved without it. -/
theorem chunk_ok_6 : countFrom (6 * 5000000) 5000000 1857859 = some 2146775 := by
  native_decide

end SunA243164.Compute
