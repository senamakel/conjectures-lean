import BachSorenson.Checker2
import BachSorenson.Compute2.Chunk0
import BachSorenson.Compute2.Chunk1
import BachSorenson.Compute2.Chunk2
import BachSorenson.Compute2.Chunk3
import BachSorenson.Compute2.Chunk4
import BachSorenson.Compute2.Chunk5
import BachSorenson.Compute2.Chunk6
import BachSorenson.Compute2.Chunk7
import BachSorenson.Compute2.Chunk8
import BachSorenson.Compute2.Chunk9
import BachSorenson.Compute2.Chunk10
import BachSorenson.Compute2.Chunk11
import BachSorenson.Compute2.Chunk12
import BachSorenson.Compute2.Chunk13
import BachSorenson.Compute2.Chunk14
import BachSorenson.Compute2.Chunk15

/-!
# The finite computation for the constant `2`, every `2 ≤ q < 2^15`

For every `q < 2^15 = 32768` with `q ≥ 2` and every `a` coprime to `q`, some prime
`p ≡ a (mod q)` satisfies `p ≤ bound2 q < 2 (q log q)²`. The checker (`BachSorensonCheck2.lean`,
core Lean only, precompiled) and its soundness theorem
`BachSorenson.Checker.exists_prime_of_checkRange2` are proved without computational trust; only
the 16 chunk evaluations `chunk2_ok_0 … chunk2_ok_15` use `native_decide`.

The largest least prime that occurs is `6188401` (below the table size `8·10^6`), and the largest
ratio `p/(2 (q log q)²)` is `0.78`, at `q = 2`.
-/

namespace BachSorenson

theorem chunk2_ok (i : ℕ) (hi : i < 16) :
    Checker.checkRange2 8000000 (i * 2048) 2048 = true := by
  interval_cases i
  exacts [chunk2_ok_0, chunk2_ok_1, chunk2_ok_2, chunk2_ok_3, chunk2_ok_4, chunk2_ok_5,
    chunk2_ok_6, chunk2_ok_7, chunk2_ok_8, chunk2_ok_9, chunk2_ok_10, chunk2_ok_11, chunk2_ok_12,
    chunk2_ok_13, chunk2_ok_14, chunk2_ok_15]

theorem bachSorenson_two_small {q a : ℕ} (hq : 2 ≤ q) (hq' : q < 2 ^ 15) (ha : a.Coprime q) :
    ∃ p : ℕ, p.Prime ∧ p ≡ a [MOD q] ∧ (p : ℝ) < 2 * ((q : ℝ) * Real.log q) ^ 2 := by
  obtain ⟨p, hp, hpa, hpb⟩ := Checker.exists_prime_of_checkRange2
    (chunk2_ok (q / 2048) (by omega)) (Nat.div_mul_le_self q 2048) (by omega) hq ha
  refine ⟨p, hp, hpa, ?_⟩
  have h1 : (p : ℝ) ≤ Checker.bound2 q := by exact_mod_cast hpb
  linarith [Checker.bound2_lt q hq]

end BachSorenson
