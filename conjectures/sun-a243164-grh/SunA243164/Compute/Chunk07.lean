import SunA243164.Compute.Checker

namespace SunA243164.Compute

/-- Chunk 7 of the finite range: the primes in `[7 * 5000000, 8 * 5000000)`, starting from
the count `π(7 * 5000000 - 1) = 2146775`.

Evaluated by `native_decide` (trust assumption `chunk_ok_7._native.native_decide.ax_*`); the
checker's soundness is `SunA243164.Compute.countFrom_sound`, proved without it. -/
theorem chunk_ok_7 : countFrom (7 * 5000000) 5000000 2146775 = some 2433654 := by
  native_decide

end SunA243164.Compute
