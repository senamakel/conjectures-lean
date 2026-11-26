import SunA243164.Compute.Checker

namespace SunA243164.Compute

/-- Chunk 12 of the finite range: the primes in `[12 * 5000000, 13 * 5000000)`, starting from
the count `π(12 * 5000000 - 1) = 3562115`.

Evaluated by `native_decide` (trust assumption `chunk_ok_12._native.native_decide.ax_*`); the
checker's soundness is `SunA243164.Compute.countFrom_sound`, proved without it. -/
theorem chunk_ok_12 : countFrom (12 * 5000000) 5000000 3562115 = some 3840554 := by
  native_decide

end SunA243164.Compute
