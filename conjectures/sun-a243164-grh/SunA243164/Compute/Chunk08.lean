import SunA243164.Compute.Checker

namespace SunA243164.Compute

/-- Chunk 8 of the finite range: the primes in `[8 * 5000000, 9 * 5000000)`, starting from
the count `π(8 * 5000000 - 1) = 2433654`.

Evaluated by `native_decide` (trust assumption `chunk_ok_8._native.native_decide.ax_*`); the
checker's soundness is `SunA243164.Compute.countFrom_sound`, proved without it. -/
theorem chunk_ok_8 : countFrom (8 * 5000000) 5000000 2433654 = some 2718160 := by
  native_decide

end SunA243164.Compute
