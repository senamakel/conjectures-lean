import GoldbachCheck

namespace Goldbach.Check

/-- Ladder chunk 67: a chain of Pocklington-certified primes with gaps `≤ 1999999999996` covering
`[67000000000000000000, 68000000000000000000]`.

This is evaluated by `native_decide`, which adds one auxiliary axiom
(`ladder_chunk_67._native.native_decide.ax_*`) asserting that the compiled evaluation of the checker
agrees with its definition. The checker and its soundness are proved without it. -/
theorem ladder_chunk_67 : ladderCover 1999999999996 67000000000000000000 68000000000000000000 = true := by
  native_decide

end Goldbach.Check
