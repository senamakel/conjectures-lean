import BachSharp.Basic
import LLS.Bach2.SoundBasic
import BachSharp.Compute.S0
import BachSharp.Compute.S1
import BachSharp.Compute.S2
import BachSharp.Compute.S3

/-!
# The sharp bound for `m < 2^17`, without GRH

`m = 3` by hand (the unit `2`, with equality `2 = (2 / log² 3) log² 3`); `4 ≤ m < 2^17` by the
generation search of ankeny-grh with `y = ⌊1.657 (logLo m 64)²⌋ ≤ 1.657 log² m`, in four
`native_decide` chunks (`BachSharp/Compute/S*.lean`), sound by `checkSmall_sound`.
-/

namespace BachSharp

open BachSharp.Check LLS.Check

theorem checkSmall_sound {lo n : ℕ} (h : checkSmall lo n = true) (q : ℕ) [NeZero q]
    (h1 : lo ≤ q) (h2 : q < lo + n) :
    Subgroup.closure (Ankeny.Checker.smallUnits q (ySmall q)) = ⊤ ∧
      (ySmall q : ℝ) ≤ 1657 / 1000 * Real.log q ^ 2 := by
  unfold checkSmall at h
  rw [List.all_eq_true] at h
  have hq := h q (List.mem_range'_1.2 ⟨h1, h2⟩)
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hq
  refine ⟨Ankeny.Checker.closure_eq_top_of_checkGen q _ hq.2, ?_⟩
  have hq1 : 1 ≤ q := Nat.pos_of_ne_zero (NeZero.ne q)
  have hlo := logLo_le q 64 hq1 (by norm_num)
  have hlo0 : (0 : ℝ) ≤ ((logLo q 64 : ℚ) : ℝ) := by exact_mod_cast logLo_nonneg q 64
  have hc : (((ySmall q : ℚ)) : ℝ) ≤ (((1657 : ℚ) / 1000 * logLo q 64 * logLo q 64 : ℚ) : ℝ) := by
    exact_mod_cast hq.1
  push_cast at hc
  nlinarith

lemma closure_three : Subgroup.closure (Ankeny.Checker.smallUnits 3 2) = ⊤ :=
  Ankeny.Checker.closure_eq_top_of_checkGen 3 2 (by decide +kernel)

/-- **The sharp bound for every modulus `q < 2^17`** (tier D, no GRH). -/
theorem sharp_small (q : ℕ) [NeZero q] (hq : q < 2 ^ 17) (H : Subgroup (ZMod q)ˣ)
    (hH : H ≠ ⊤) : ∃ a : (ZMod q)ˣ, a ∉ H ∧ ((a : ZMod q).val : ℝ) ≤ sharpConst * Real.log q ^ 2 := by
  rcases Nat.lt_or_ge q 3 with h3 | h3
  · exact absurd (Ankeny.subgroup_eq_top_of_le_two (by omega) H) hH
  have hlq : 0 ≤ Real.log q ^ 2 := sq_nonneg _
  have hmono : ∀ y : ℕ, (y : ℝ) ≤ 1657 / 1000 * Real.log q ^ 2 →
      (y : ℝ) ≤ sharpConst * Real.log q ^ 2 := fun y hy =>
    hy.trans (mul_le_mul_of_nonneg_right c1657_le_sharpConst hlq)
  have hfin : ∀ y : ℕ, Subgroup.closure (Ankeny.Checker.smallUnits q y) = ⊤ →
      (y : ℝ) ≤ sharpConst * Real.log q ^ 2 →
      ∃ a : (ZMod q)ˣ, a ∉ H ∧ ((a : ZMod q).val : ℝ) ≤ sharpConst * Real.log q ^ 2 := by
    intro y hy hyc
    obtain ⟨a, ha, hle⟩ := exists_not_mem_of_closure hy H hH
    exact ⟨a, ha, hle.trans hyc⟩
  rcases Nat.eq_or_lt_of_le h3 with h | h
  · subst h
    refine hfin 2 closure_three ?_
    have := sharpConst_mul_log_three_sq
    push_cast
    linarith
  have hcase : ∀ {lo n : ℕ}, checkSmall lo n = true → lo ≤ q → q < lo + n →
      ∃ a : (ZMod q)ˣ, a ∉ H ∧ ((a : ZMod q).val : ℝ) ≤ sharpConst * Real.log q ^ 2 := by
    intro lo n hc h1 h2
    obtain ⟨hcl, hy⟩ := checkSmall_sound hc q h1 h2
    exact hfin _ hcl (hmono _ hy)
  rcases Nat.lt_or_ge q (2 ^ 14) with h14 | h14
  · exact hcase small_ok_S0 (by omega) (by omega)
  rcases Nat.lt_or_ge q (2 ^ 15) with h15 | h15
  · exact hcase small_ok_S1 h14 (by omega)
  rcases Nat.lt_or_ge q (2 ^ 16) with h16 | h16
  · exact hcase small_ok_S2 h15 (by omega)
  · exact hcase small_ok_S3 h16 (by omega)

end BachSharp
