import GoldbachCheck

namespace Goldbach.Check

/-- Binary Goldbach chunk 78: every even `m` in `[6 + 78 * 10000000000, 6 + 79 * 10000000000)` is
`p + q` with `p ≤ 9999` an odd prime.

This is evaluated by `native_decide`, which adds one auxiliary axiom
(`binary_chunk_78._native.native_decide.ax_*`) asserting that the compiled evaluation of the checker
agrees with its definition. The checker and its soundness are proved without it. -/
theorem binary_chunk_78 : goldbachChunk 9999 (6 + 78 * 10000000000) 500000 10000 = true := by
  native_decide

end Goldbach.Check
