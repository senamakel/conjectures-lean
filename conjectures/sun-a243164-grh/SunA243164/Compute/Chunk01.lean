import SunA243164.Compute.Checker

namespace SunA243164.Compute

/-- Chunk 1 of the finite range: the primes in `[1 * 5000000, 2 * 5000000)`, starting from
the count `π(1 * 5000000 - 1) = 348513`.

Evaluated by `native_decide` (trust assumption `chunk_ok_1._native.native_decide.ax_*`); the
checker's soundness is `SunA243164.Compute.countFrom_sound`, proved without it. -/
theorem chunk_ok_1 : countFrom (1 * 5000000) 5000000 348513 = some 664579 := by
  native_decide

end SunA243164.Compute
