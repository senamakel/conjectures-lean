import SunA243164.Compute.Checker

namespace SunA243164.Compute

/-- Chunk 18 of the finite range: the primes in `[18 * 5000000, 19 * 5000000)`, starting from
the count `π(18 * 5000000 - 1) = 5216954`.

Evaluated by `native_decide` (trust assumption `chunk_ok_18._native.native_decide.ax_*`); the
checker's soundness is `SunA243164.Compute.countFrom_sound`, proved without it. -/
theorem chunk_ok_18 : countFrom (18 * 5000000) 5000000 5216954 = some 5489749 := by
  native_decide

end SunA243164.Compute
