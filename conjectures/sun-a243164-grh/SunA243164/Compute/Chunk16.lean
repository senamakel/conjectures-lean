import SunA243164.Compute.Checker

namespace SunA243164.Compute

/-- Chunk 16 of the finite range: the primes in `[16 * 5000000, 17 * 5000000)`, starting from
the count `π(16 * 5000000 - 1) = 4669382`.

Evaluated by `native_decide` (trust assumption `chunk_ok_16._native.native_decide.ax_*`); the
checker's soundness is `SunA243164.Compute.countFrom_sound`, proved without it. -/
theorem chunk_ok_16 : countFrom (16 * 5000000) 5000000 4669382 = some 4943731 := by
  native_decide

end SunA243164.Compute
