import SunA243164.Compute.Checker

namespace SunA243164.Compute

/-- Chunk 10 of the finite range: the primes in `[10 * 5000000, 11 * 5000000)`, starting from
the count `π(10 * 5000000 - 1) = 3001134`.

Evaluated by `native_decide` (trust assumption `chunk_ok_10._native.native_decide.ax_*`); the
checker's soundness is `SunA243164.Compute.countFrom_sound`, proved without it. -/
theorem chunk_ok_10 : countFrom (10 * 5000000) 5000000 3001134 = some 3282200 := by
  native_decide

end SunA243164.Compute
