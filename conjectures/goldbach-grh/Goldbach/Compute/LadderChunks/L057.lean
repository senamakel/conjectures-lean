import GoldbachCheck

namespace Goldbach.Check

/-- Ladder chunk 57: a chain of Pocklington-certified primes with gaps `≤ 1999999999996` covering
`[57000000000000000000, 58000000000000000000]`.

This is evaluated by `native_decide`, which adds one auxiliary axiom
(`ladder_chunk_57._native.native_decide.ax_*`) asserting that the compiled evaluation of the checker
agrees with its definition. The checker and its soundness are proved without it. -/
theorem ladder_chunk_57 : ladderCover 1999999999996 57000000000000000000 58000000000000000000 = true := by
  native_decide

end Goldbach.Check
