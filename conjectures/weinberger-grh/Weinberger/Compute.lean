import Weinberger.Compute.Checker
import Weinberger.Compute.Chunk00
import Weinberger.Compute.Chunk01
import Weinberger.Compute.Chunk02
import Weinberger.Compute.Chunk03
import Weinberger.Compute.Chunk04
import Weinberger.Compute.Chunk05
import Weinberger.Compute.Chunk06
import Weinberger.Compute.Chunk07
import Weinberger.Compute.Chunk08
import Weinberger.Compute.Chunk09

/-!
# The finite range `n < 10^8` (verified computation)

`checkFrom 0 (10^8) = true` is split into 10 chunks of `10^7`, each closed by `native_decide`
(files `Weinberger/Compute/ChunkNN.lean`, built in parallel). A separate `native_decide`
(`known_noRep`) runs the exhaustive search `repB` on the 65 numbers. The checkers and their
soundness (`okN_sound`, `isIdoneal_of_repB`) are proved in `Weinberger.Compute.Checker`.
-/

namespace Weinberger.Compute

open Idoneal

theorem check_ok : checkFrom 0 (10 ^ 8) = true := by
  rw [show 10 ^ 8 = 10 * 10000000 by norm_num]
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

/-- The exhaustive search finds no representation of any of the 65 numbers. -/
theorem known_noRep : ∀ n ∈ knownIdonealNumbers, repB n = false := by
  native_decide

end Weinberger.Compute

namespace Weinberger

open Idoneal

/-- Every idoneal `n < 10^8` is one of the 65. -/
theorem mem_known_of_isIdoneal_of_lt {n : ℕ} (hn : IsIdoneal n) (hlt : n < 10 ^ 8) :
    n ∈ knownIdonealNumbers :=
  Compute.okN_sound (Compute.checkFrom_sound _ 0 Compute.check_ok n (Nat.zero_le _) (by omega)) hn

/-- The 65 numbers are idoneal (unconditional). -/
theorem knownIdonealNumbers_are_idoneal : ∀ n ∈ knownIdonealNumbers, IsIdoneal n := by
  intro n hn
  refine Compute.isIdoneal_of_repB ?_ (Compute.known_noRep n hn)
  have : 0 ∉ knownIdonealNumbers := by simp [knownIdonealNumbers]
  exact Nat.pos_of_ne_zero fun h => this (h ▸ hn)

end Weinberger
