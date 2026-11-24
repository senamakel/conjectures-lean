import Ankeny.Finite
import LLS.Compute.C114_0
import LLS.Compute.C114_1
import LLS.Compute.C114_2
import LLS.Compute.C114_3
import LLS.Compute.C114_4
import LLS.Compute.C114_5
import LLS.Compute.C114_6
import LLS.Compute.C114_7
import LLS.Compute.C114_8
import LLS.Compute.C114_9
import LLS.Compute.C114_10
import LLS.Compute.C114_11
import LLS.Compute.C114_12
import LLS.Compute.C114_13
import LLS.Compute.C114_14
import LLS.Compute.C114_15

/-!
# The finite range `q < 2^18` with constant `11/4`

ankeny-grh's generation checker (`Ankeny.Checker.checkRange`, soundness
`Ankeny.bach_of_checkRange`) run with `c = 11/4`: for every `4 ≤ q < 2^18` the units of
residue `≤ ⌊(11/4) (⌊log₂ q⌋ log 2)²⌋ ≤ (11/4) log² q` generate `(ZMod q)ˣ`. The case `q = 3`
(where `⌊log₂ 3⌋ = 1` makes the checker's bound too small) is done by hand.
-/

namespace LLS

theorem bach_three' (H : Subgroup (ZMod 3)ˣ) (hH : H ≠ ⊤) :
    ∃ a : (ZMod 3)ˣ, a ∉ H ∧ ((a : ZMod 3).val : ℝ) ≤ 11 / 4 * Real.log (3 : ℕ) ^ 2 := by
  obtain ⟨a, ha⟩ : ∃ a, a ∉ H := by
    by_contra h
    push Not at h
    exact hH (eq_top_iff.2 fun a _ => h a)
  refine ⟨a, ha, ?_⟩
  have hv : (a : ZMod 3).val ≤ 2 := Nat.lt_succ_iff.1 (ZMod.val_lt _)
  have hl : 1 ≤ Real.log (3 : ℕ) := by
    rw [Real.le_log_iff_exp_le (by norm_num)]
    have := Real.exp_one_lt_d9
    push_cast; linarith
  have : ((a : ZMod 3).val : ℝ) ≤ 2 := by exact_mod_cast hv
  have h2 : 1 ≤ Real.log (3 : ℕ) ^ 2 := by nlinarith
  calc ((a : ZMod 3).val : ℝ) ≤ 2 := this
    _ ≤ 11 / 4 * 1 := by norm_num
    _ ≤ 11 / 4 * Real.log (3 : ℕ) ^ 2 := by gcongr

theorem bach_small114 (q : ℕ) [NeZero q] (hq : q < 2 ^ 18) (H : Subgroup (ZMod q)ˣ) (hH : H ≠ ⊤) :
    ∃ a : (ZMod q)ˣ, a ∉ H ∧ ((a : ZMod q).val : ℝ) ≤ 11 / 4 * Real.log q ^ 2 := by
  rcases lt_or_ge q 4 with h4 | h4
  · rcases lt_or_ge q 3 with h3 | h3
    · exact absurd (Ankeny.subgroup_eq_top_of_le_two (by omega) H) hH
    · obtain rfl : q = 3 := by omega
      exact bach_three' H hH
  have hc : ∀ i < 16, Ankeny.Checker.checkRange 11 4 (if i = 0 then 4 else i * 16384)
        ((i + 1) * 16384 - if i = 0 then 4 else i * 16384) = true := by
    intro i hi
    interval_cases i
    exacts [chunk114_ok_0, chunk114_ok_1, chunk114_ok_2, chunk114_ok_3, chunk114_ok_4, chunk114_ok_5, chunk114_ok_6, chunk114_ok_7, chunk114_ok_8, chunk114_ok_9, chunk114_ok_10, chunk114_ok_11, chunk114_ok_12, chunk114_ok_13, chunk114_ok_14, chunk114_ok_15]
  set i := q / 16384 with hi
  have hi16 : i < 16 := by omega
  have hlo : (if i = 0 then 4 else i * 16384) ≤ q := by split_ifs <;> omega
  have hhi : q < (if i = 0 then 4 else i * 16384)
      + ((i + 1) * 16384 - if i = 0 then 4 else i * 16384) := by split_ifs <;> omega
  have h := Ankeny.bach_of_checkRange (by norm_num) (hc i hi16) q hlo hhi H hH
  have e : ((11 : ℕ) : ℝ) / ((4 : ℕ) : ℝ) = 11 / 4 := by norm_num
  simpa [e] using h

end LLS
