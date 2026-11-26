import GoldbachCheck

namespace Goldbach.Check

/-- Ladder chunk 56: a chain of Pocklington-certified primes with gaps `≤ 1999999999996` covering
`[56000000000000000000, 57000000000000000000]`.

This is evaluated by `native_decide`, which adds one auxiliary axiom
(`ladder_chunk_56._native.native_decide.ax_*`) asserting that the compiled evaluation of the checker
agrees with its definition. The checker and its soundness are proved without it. -/
theorem ladder_chunk_56 : ladderCover 1999999999996 56000000000000000000 57000000000000000000 = true := by
  native_decide

end Goldbach.Check
