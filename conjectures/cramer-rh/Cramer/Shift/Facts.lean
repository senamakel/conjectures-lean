import Cramer.Shift.Data
import Cramer.Shift.Tail
import Cramer.Shift.Bucket

/-!
# The checked facts about the majorant `maj107`

Everything here is evaluated by `decide` in the kernel: the cells cover `[0, 150]`, the tail
check holds from `x = 150`, each term has a valid bucket, and the two sums are
`SS ≤ 0.5336`, `NS ≤ 0.207`.
-/

namespace Cramer.Shift

set_option maxRecDepth 100000 in
theorem maj107_buckets : maj107.all (fun c => bucketOK c.2.1 c.2.2 (nb c.2.1 c.2.2)) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem maj107_tail : tailOK maj107 150000000 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem maj107_SSn : SSn maj107 ≤ 533600000000000 := by decide +kernel

set_option maxRecDepth 100000 in
theorem maj107_NSn : NSn maj107 ≤ 207000000000000 := by decide +kernel

theorem cells107_all : cells107.all (cellOK maj107) = true := by
  simp only [cells107, List.all_append, cells107_0_ok, cells107_1_ok, cells107_2_ok, cells107_3_ok,
    cells107_4_ok, cells107_5_ok, cells107_6_ok, cells107_7_ok, cells107_8_ok, cells107_9_ok,
    Bool.and_self]

/-- **Every `y ≥ 0` is good for `maj107`.** -/
theorem good107 : ∀ y : ℝ, 0 ≤ y → CellGood maj107 y :=
  all_good cells107_chain cells107_all maj107_tail

theorem buckets107 : ∀ c ∈ maj107, bucketOK c.2.1 c.2.2 (nb c.2.1 c.2.2) = true :=
  fun c hc => List.all_eq_true.mp maj107_buckets c hc

theorem SS107 : (SSn maj107 : ℝ) / (KC * NN) ≤ 0.5336 := by
  have h : (SSn maj107 : ℝ) ≤ 533600000000000 := by exact_mod_cast maj107_SSn
  rw [div_le_iff₀ (by norm_num [KC, NN])]
  have e : (0.5336 : ℝ) * (KC * NN) = 533600000000000 := by norm_num [KC, NN]
  rw [e]; exact h

theorem NS107 : (NSn maj107 : ℝ) / (KC * NN) ≤ 0.207 := by
  have h : (NSn maj107 : ℝ) ≤ 207000000000000 := by exact_mod_cast maj107_NSn
  rw [div_le_iff₀ (by norm_num [KC, NN])]
  have e : (0.207 : ℝ) * (KC * NN) = 207000000000000 := by norm_num [KC, NN]
  rw [e]; exact h

end Cramer.Shift
