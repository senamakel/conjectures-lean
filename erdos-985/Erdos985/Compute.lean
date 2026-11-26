import Erdos985.Statement
import Erdos985.Compute.Checker
import Erdos985.Compute.Chunk00
import Erdos985.Compute.Chunk01
import Erdos985.Compute.Chunk02
import Erdos985.Compute.Chunk03
import Erdos985.Compute.Chunk04
import Erdos985.Compute.Chunk05
import Erdos985.Compute.Chunk06
import Erdos985.Compute.Chunk07
import Erdos985.Compute.Chunk08
import Erdos985.Compute.Chunk09
import Erdos985.Compute.Chunk10
import Erdos985.Compute.Chunk11
import Erdos985.Compute.Chunk12
import Erdos985.Compute.Chunk13
import Erdos985.Compute.Chunk14
import Erdos985.Compute.Chunk15
import Erdos985.Compute.Chunk16
import Erdos985.Compute.Chunk17
import Erdos985.Compute.Chunk18
import Erdos985.Compute.Chunk19

/-!
# Every odd prime `p < 10^8` has a prime primitive root below `p`  (verified computation)

The checker `Erdos985.Compute.checkAll` and its soundness theorem
`Erdos985.Compute.checkAll_sound` live in `Erdos985.Compute.Checker` and are proved
without any computational trust assumptions.  The evaluation `checkAll (10^8) = true` is
split into 20 chunks of `5 * 10^6` (files `Erdos985/Compute/ChunkNN.lean`, built in
parallel), each discharged by `native_decide`.
-/

namespace Erdos985.Compute

theorem checkFrom_chunks (c : ℕ) :
    ∀ j, (∀ i < j, checkFrom (i * c) c = true) → checkFrom 0 (j * c) = true
  | 0, _ => by simp [checkFrom]
  | j + 1, h => by
    rw [Nat.succ_mul, checkFrom_add, checkFrom_chunks c j (fun i hi => h i (by omega)),
      Nat.zero_add, h j (by omega), Bool.and_self]

/-- The full verified computation `checkAll (10^8) = true`.

This assembles the chunk lemmas `chunk_ok_0`, …, `chunk_ok_19`, each of which is proved by
`native_decide` and therefore adds a trust assumption: one auxiliary axiom per chunk
(`chunk_ok_N._native.native_decide.ax_*`, the per-use successor of `Lean.ofReduceBool`)
asserting that the compiled/interpreted evaluation of `checkFrom` agrees with its kernel
definition. -/
theorem check_ok : checkAll (10 ^ 8) = true := by
  rw [checkAll, show 10 ^ 8 = 20 * 5000000 by norm_num]
  apply checkFrom_chunks
  intro i hi
  interval_cases i
  · exact chunk_ok_0
  · exact chunk_ok_1
  · exact chunk_ok_2
  · exact chunk_ok_3
  · exact chunk_ok_4
  · exact chunk_ok_5
  · exact chunk_ok_6
  · exact chunk_ok_7
  · exact chunk_ok_8
  · exact chunk_ok_9
  · exact chunk_ok_10
  · exact chunk_ok_11
  · exact chunk_ok_12
  · exact chunk_ok_13
  · exact chunk_ok_14
  · exact chunk_ok_15
  · exact chunk_ok_16
  · exact chunk_ok_17
  · exact chunk_ok_18
  · exact chunk_ok_19

end Erdos985.Compute

namespace Erdos985

theorem small_primes_have_prime_primitive_root (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2)
    (hlt : p < 10 ^ 8) : ∃ q, q.Prime ∧ q < p ∧ orderOf (q : ZMod p) = p - 1 :=
  Erdos985.Compute.checkAll_sound Erdos985.Compute.check_ok p hp hp2 hlt

end Erdos985
