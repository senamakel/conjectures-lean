import Ankeny.Statement
import Ankeny.Checker

/-!
# The finite range: from the checker to Bach's bound

`yOf cn cd q = ⌊(cn/cd) (⌊log₂ q⌋ · 0.6931471803)²⌋ ≤ (cn/cd) log² q`. If
`checkRange cn cd lo n` holds, then for every `q ∈ [lo, lo + n)` the units of residue
`≤ yOf cn cd q` generate `(ZMod q)ˣ` (or `q ≤ 2` and the group is
trivial), so every proper subgroup omits one of them.
-/

namespace Ankeny

open Checker

lemma yOf_le (cn cd q : ℕ) (hcd : 0 < cd) (hq : q ≠ 0) :
    (yOf cn cd q : ℝ) ≤ (cn / cd : ℝ) * Real.log q ^ 2 := by
  set k := Nat.log 2 q
  have hk : Nat.log2 q = k := Nat.log2_eq_log_two
  have hpow : 2 ^ k ≤ q := Nat.pow_log_le_self 2 hq
  have hl2 := Real.log_two_gt_d9
  have hlog : (k : ℝ) * 0.6931471803 ≤ Real.log q := by
    have h1 : Real.log ((2 : ℝ) ^ k) ≤ Real.log q :=
      Real.log_le_log (by positivity) (by exact_mod_cast hpow)
    rw [Real.log_pow] at h1
    have : (k : ℝ) * 0.6931471803 ≤ k * Real.log 2 :=
      mul_le_mul_of_nonneg_left hl2.le (Nat.cast_nonneg _)
    linarith
  have h0 : (0 : ℝ) ≤ (k : ℝ) * 0.6931471803 := by positivity
  have hcdR : (0 : ℝ) < cd := by exact_mod_cast hcd
  unfold yOf
  rw [hk]
  calc (((cn * k ^ 2 * 6931471803 ^ 2 / (cd * 10 ^ 20) : ℕ)) : ℝ)
        ≤ ((cn * k ^ 2 * 6931471803 ^ 2 : ℕ) : ℝ) / ((cd * 10 ^ 20 : ℕ) : ℝ) :=
        Nat.cast_div_le
    _ = (cn / cd : ℝ) * ((k : ℝ) * 0.6931471803) ^ 2 := by
        push_cast; field_simp; ring
    _ ≤ (cn / cd : ℝ) * Real.log q ^ 2 := by gcongr

lemma subgroup_eq_top_of_le_two {q : ℕ} [NeZero q] (hq : q ≤ 2) (H : Subgroup (ZMod q)ˣ) :
    H = ⊤ := by
  have hcard : Fintype.card (ZMod q)ˣ ≤ 1 := by
    rw [ZMod.card_units_eq_totient]
    interval_cases q <;> simp at *
  have : Subsingleton (ZMod q)ˣ := Fintype.card_le_one_iff_subsingleton.1 hcard
  exact eq_top_iff.2 fun a _ => (Subsingleton.elim a 1) ▸ H.one_mem

theorem bach_of_checkRange {cn cd lo n : ℕ} (hcd : 0 < cd)
    (h : checkRange cn cd lo n = true) (q : ℕ) [NeZero q] (hq1 : lo ≤ q) (hq2 : q < lo + n)
    (H : Subgroup (ZMod q)ˣ) (hH : H ≠ ⊤) :
    ∃ a : (ZMod q)ˣ, a ∉ H ∧ ((a : ZMod q).val : ℝ) ≤ (cn / cd : ℝ) * Real.log q ^ 2 := by
  have hq' := List.all_eq_true.1 h q (List.mem_range'_1.2 ⟨hq1, hq2⟩)
  simp only [Bool.or_eq_true, decide_eq_true_eq] at hq'
  rcases hq' with hle | hchk
  · exact absurd (subgroup_eq_top_of_le_two hle H) hH
  have htop := closure_eq_top_of_checkGen q (yOf cn cd q) hchk
  by_contra hcon
  push Not at hcon
  apply hH
  rw [eq_top_iff, ← htop, Subgroup.closure_le]
  intro u hu
  by_contra huH
  have h1 := hcon u huH
  have h2 : ((u : ZMod q).val : ℝ) ≤ yOf cn cd q := by exact_mod_cast hu
  have h3 := yOf_le cn cd q hcd (NeZero.ne q)
  linarith

end Ankeny
