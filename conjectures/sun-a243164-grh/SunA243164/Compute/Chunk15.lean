import SunA243164.Compute.Checker

namespace SunA243164.Compute

/-- Chunk 15 of the finite range: the primes in `[15 * 5000000, 16 * 5000000)`, starting from
the count `π(15 * 5000000 - 1) = 4394304`.

Evaluated by `native_decide` (trust assumption `chunk_ok_15._native.native_decide.ax_*`); the
checker's soundness is `SunA243164.Compute.countFrom_sound`, proved without it. -/
theorem chunk_ok_15 : countFrom (15 * 5000000) 5000000 4394304 = some 4669382 := by
  native_decide

end SunA243164.Compute
