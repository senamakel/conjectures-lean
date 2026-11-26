import SunA243164.Compute.Checker

namespace SunA243164.Compute

/-- Chunk 0 of the finite range: the primes in `[0 * 5000000, 1 * 5000000)`, starting from
the count `π(0 * 5000000 - 1) = 0`.

Evaluated by `native_decide` (trust assumption `chunk_ok_0._native.native_decide.ax_*`); the
checker's soundness is `SunA243164.Compute.countFrom_sound`, proved without it. -/
theorem chunk_ok_0 : countFrom (0 * 5000000) 5000000 0 = some 348513 := by
  native_decide

end SunA243164.Compute
