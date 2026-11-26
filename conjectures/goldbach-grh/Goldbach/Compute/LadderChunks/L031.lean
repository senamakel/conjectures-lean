import GoldbachCheck

namespace Goldbach.Check

/-- Ladder chunk 31: a chain of Pocklington-certified primes with gaps `≤ 1999999999996` covering
`[31000000000000000000, 32000000000000000000]`.

This is evaluated by `native_decide`, which adds one auxiliary axiom
(`ladder_chunk_31._native.native_decide.ax_*`) asserting that the compiled evaluation of the checker
agrees with its definition. The checker and its soundness are proved without it. -/
theorem ladder_chunk_31 : ladderCover 1999999999996 31000000000000000000 32000000000000000000 = true := by
  native_decide

end Goldbach.Check
