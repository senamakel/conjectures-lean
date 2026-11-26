import SunA243164.Compute.Checker

namespace SunA243164.Compute

/-- Chunk 11 of the finite range: the primes in `[11 * 5000000, 12 * 5000000)`, starting from
the count `π(11 * 5000000 - 1) = 3282200`.

Evaluated by `native_decide` (trust assumption `chunk_ok_11._native.native_decide.ax_*`); the
checker's soundness is `SunA243164.Compute.countFrom_sound`, proved without it. -/
theorem chunk_ok_11 : countFrom (11 * 5000000) 5000000 3282200 = some 3562115 := by
  native_decide

end SunA243164.Compute
