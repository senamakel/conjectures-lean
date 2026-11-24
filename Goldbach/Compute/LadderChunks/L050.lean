import GoldbachCheck

namespace Goldbach.Check

/-- Ladder chunk 50: a chain of Pocklington-certified primes with gaps `≤ 1999999999996` covering
`[50000000000000000000, 51000000000000000000]`.

This is evaluated by `native_decide`, which adds one auxiliary axiom
(`ladder_chunk_50._native.native_decide.ax_*`) asserting that the compiled evaluation of the checker
agrees with its definition. The checker and its soundness are proved without it. -/
theorem ladder_chunk_50 : ladderCover 1999999999996 50000000000000000000 51000000000000000000 = true := by
  native_decide

end Goldbach.Check
