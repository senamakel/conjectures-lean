import PrimitiveRootSq.Compute.Checker
import PrimitiveRootSq.Compute.Chunk00
import PrimitiveRootSq.Compute.Chunk01
import PrimitiveRootSq.Compute.Chunk02
import PrimitiveRootSq.Compute.Chunk03
import PrimitiveRootSq.Compute.Chunk04
import PrimitiveRootSq.Compute.Chunk05
import PrimitiveRootSq.Compute.Chunk06
import PrimitiveRootSq.Compute.Chunk07
import PrimitiveRootSq.Compute.Chunk08
import PrimitiveRootSq.Compute.Chunk09
import PrimitiveRootSq.Compute.Chunk10
import PrimitiveRootSq.Compute.Chunk11
import PrimitiveRootSq.Compute.Chunk12
import PrimitiveRootSq.Compute.Chunk13
import PrimitiveRootSq.Compute.Chunk14
import PrimitiveRootSq.Compute.Chunk15
import PrimitiveRootSq.Compute.Chunk16
import PrimitiveRootSq.Compute.Chunk17
import PrimitiveRootSq.Compute.Chunk18
import PrimitiveRootSq.Compute.Chunk19

/-!
# Every odd prime `p < 10^8` has a prime `q < p` that is a primitive root modulo `p²`
(verified computation)

The checker `PrimitiveRootSq.Compute.checkAll` and its soundness theorem
`PrimitiveRootSq.Compute.checkAll_sound` are proved in `PrimitiveRootSq.Compute.Checker`. The
evaluation `checkAll (10^8) = true` is split into 20 chunks of `5 * 10^6`, each discharged by
`native_decide` (one auxiliary axiom `chunk_ok_N._native.native_decide.ax_*` per chunk).
-/

namespace PrimitiveRootSq.Compute

theorem checkFrom_chunks (c : ℕ) :
    ∀ j, (∀ i < j, checkFrom (i * c) c = true) → checkFrom 0 (j * c) = true
  | 0, _ => by simp [checkFrom]
  | j + 1, h => by
    rw [Nat.succ_mul, checkFrom_add, checkFrom_chunks c j (fun i hi => h i (by omega)),
      Nat.zero_add, h j (by omega), Bool.and_self]

/-- The full verified computation `checkAll (10^8) = true`. -/
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

end PrimitiveRootSq.Compute

namespace PrimitiveRootSq

theorem small_primes_good (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (hlt : p < 10 ^ 8) :
    ∃ q, q.Prime ∧ q < p ∧ orderOf (q : ZMod p) = p - 1 ∧ (q : ZMod (p ^ 2)) ^ (p - 1) ≠ 1 :=
  Compute.checkAll_sound Compute.check_ok p hp hp2 hlt

end PrimitiveRootSq
