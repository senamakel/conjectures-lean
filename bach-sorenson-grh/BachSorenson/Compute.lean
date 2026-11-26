import BachSorenson.Checker
import BachSorenson.Compute.Chunk0
import BachSorenson.Compute.Chunk1
import BachSorenson.Compute.Chunk2
import BachSorenson.Compute.Chunk3
import BachSorenson.Compute.Chunk4
import BachSorenson.Compute.Chunk5
import BachSorenson.Compute.Chunk6
import BachSorenson.Compute.Chunk7
import BachSorenson.Compute.Chunk8
import BachSorenson.Compute.Chunk9
import BachSorenson.Compute.Chunk10
import BachSorenson.Compute.Chunk11
import BachSorenson.Compute.Chunk12
import BachSorenson.Compute.Chunk13
import BachSorenson.Compute.Chunk14
import BachSorenson.Compute.Chunk15

/-!
# Step 8: the finite computation, every `2 ≤ q < 2^15`

For every `q < 2^15 = 32768` with `q ≥ 2` and every `a` coprime to `q`, some prime
`p ≡ a (mod q)` lies below `bound q ≤ (7/2) (q log q)²`. The checker (`BachSorensonCheck.lean`,
core Lean only, precompiled to native code) and its soundness theorem
`BachSorenson.Checker.exists_prime_of_checkRange` are proved without computational trust; only
the 16 chunk evaluations `chunk_ok_0 … chunk_ok_15` use `native_decide`.

**Trust assumption.** Each `native_decide` adds one auxiliary axiom
(`BachSorenson.chunk_ok_N._native.native_decide.ax_*`) asserting that the compiled evaluation
agrees with the kernel definition. Kernel `decide` is out of reach (about `2·10^9` table lookups
plus an `8·10^6`-entry trial-division prime table per chunk).
-/

namespace BachSorenson

theorem chunk_ok (i : ℕ) (hi : i < 16) : Checker.checkRange 8000000 (i * 2048) 2048 = true := by
  interval_cases i
  exacts [chunk_ok_0, chunk_ok_1, chunk_ok_2, chunk_ok_3, chunk_ok_4, chunk_ok_5, chunk_ok_6, chunk_ok_7, chunk_ok_8, chunk_ok_9, chunk_ok_10, chunk_ok_11, chunk_ok_12, chunk_ok_13, chunk_ok_14, chunk_ok_15]

theorem bachSorenson_small {q a : ℕ} (hq : 2 ≤ q) (hq' : q < 2 ^ 15) (ha : a.Coprime q) :
    ∃ p : ℕ, p.Prime ∧ p ≡ a [MOD q] ∧ (p : ℝ) < 7 / 2 * ((q : ℝ) * Real.log q) ^ 2 := by
  obtain ⟨p, hp, hpa, hpb⟩ := Checker.exists_prime_of_checkRange
    (chunk_ok (q / 2048) (by omega)) (Nat.div_mul_le_self q 2048) (by omega) hq ha
  refine ⟨p, hp, hpa, ?_⟩
  have h1 : (p : ℝ) < Checker.bound q := by exact_mod_cast hpb
  linarith [Checker.bound_le q (by omega)]

end BachSorenson
