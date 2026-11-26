import GoldbachCheck

namespace Goldbach.Check

/-- Ladder chunk 36: a chain of Pocklington-certified primes with gaps `≤ 1999999999996` covering
`[36000000000000000000, 37000000000000000000]`.

This is evaluated by `native_decide`, which adds one auxiliary axiom
(`ladder_chunk_36._native.native_decide.ax_*`) asserting that the compiled evaluation of the checker
agrees with its definition. The checker and its soundness are proved without it. -/
theorem ladder_chunk_36 : ladderCover 1999999999996 36000000000000000000 37000000000000000000 = true := by
  native_decide

end Goldbach.Check
