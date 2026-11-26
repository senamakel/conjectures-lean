import Ankeny.Finite
import Ankeny.Compute.Chunk0
import Ankeny.Compute.Chunk1
import Ankeny.Compute.Chunk2
import Ankeny.Compute.Chunk3
import Ankeny.Compute.Chunk4
import Ankeny.Compute.Chunk5
import Ankeny.Compute.Chunk6
import Ankeny.Compute.Chunk7

/-!
# The finite computation: every `q < 2^17` is checked

For every `q < 2^17 = 131072` with `q ≥ 3`, the units of `(ZMod q)ˣ` with residue
`≤ yOf 21 5 q ≤ (21/5) log² q` generate the whole group. The checker (`AnkenyCheck.lean`, core
Lean only, precompiled to native code) and its soundness theorem
`Ankeny.Checker.closure_eq_top_of_checkGen` are proved without computational trust; only the
eight chunk evaluations `chunk_ok_0 … chunk_ok_7` use `native_decide`.

**Trust assumption.** Each `native_decide` adds one auxiliary axiom
(`Ankeny.chunk_ok_N._native.native_decide.ax_*`) asserting that the compiled evaluation agrees
with the kernel definition. Kernel `decide` is far out of reach (about `10^10` array steps).
-/

namespace Ankeny

theorem chunk_ok (i : ℕ) (hi : i < 8) : Checker.checkRange 21 5 (i * 16384) 16384 = true := by
  interval_cases i
  exacts [chunk_ok_0, chunk_ok_1, chunk_ok_2, chunk_ok_3, chunk_ok_4, chunk_ok_5, chunk_ok_6,
    chunk_ok_7]

theorem bach_small (q : ℕ) [NeZero q] (hq : q < 2 ^ 17) (H : Subgroup (ZMod q)ˣ) (hH : H ≠ ⊤) :
    ∃ a : (ZMod q)ˣ, a ∉ H ∧ ((a : ZMod q).val : ℝ) ≤ 21 / 5 * Real.log q ^ 2 := by
  have h := bach_of_checkRange (by norm_num) (chunk_ok (q / 16384) (by omega)) q
    (Nat.div_mul_le_self q 16384) (by omega) H hH
  simpa using h

end Ankeny
