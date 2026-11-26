import SunA243164.Compute.Checker

namespace SunA243164.Compute

/-- Chunk 2 of the finite range: the primes in `[2 * 5000000, 3 * 5000000)`, starting from
the count `π(2 * 5000000 - 1) = 664579`.

Evaluated by `native_decide` (trust assumption `chunk_ok_2._native.native_decide.ax_*`); the
checker's soundness is `SunA243164.Compute.countFrom_sound`, proved without it. -/
theorem chunk_ok_2 : countFrom (2 * 5000000) 5000000 664579 = some 970704 := by
  native_decide

end SunA243164.Compute
