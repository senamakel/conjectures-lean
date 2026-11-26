import SunA243164.Compute.Checker

namespace SunA243164.Compute

/-- Chunk 9 of the finite range: the primes in `[9 * 5000000, 10 * 5000000)`, starting from
the count `π(9 * 5000000 - 1) = 2718160`.

Evaluated by `native_decide` (trust assumption `chunk_ok_9._native.native_decide.ax_*`); the
checker's soundness is `SunA243164.Compute.countFrom_sound`, proved without it. -/
theorem chunk_ok_9 : countFrom (9 * 5000000) 5000000 2718160 = some 3001134 := by
  native_decide

end SunA243164.Compute
