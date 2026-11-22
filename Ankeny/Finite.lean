import Ankeny.Statement
import Ankeny.Checker

/-!
# The finite range: from the checker to Bach's bound

`yOf q = ⌊5 (⌊log₂ q⌋ · 0.6931471803)²⌋ ≤ 5 log² q`. If `allOK n` holds, then for every
`q < n` the units of residue `≤ yOf q` generate `(ZMod q)ˣ` (or `q ≤ 2` and the group is
trivial), so every proper subgroup omits one of them.
-/

namespace Ankeny

open Checker

/-- A certified lower bound for `5 log² q`. -/
def yOf (q : ℕ) : ℕ := 5 * (Nat.log 2 q) ^ 2 * 6931471803 ^ 2 / 10 ^ 20

lemma yOf_le (q : ℕ) (hq : q ≠ 0) : (yOf q : ℝ) ≤ 5 * Real.log q ^ 2 := by
  set k := Nat.log 2 q
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
  calc (yOf q : ℝ) ≤ ((5 * k ^ 2 * 6931471803 ^ 2 : ℕ) : ℝ) / ((10 ^ 20 : ℕ) : ℝ) :=
        Nat.cast_div_le
    _ = 5 * ((k : ℝ) * 0.6931471803) ^ 2 := by push_cast; ring
    _ ≤ 5 * Real.log q ^ 2 := by gcongr

/-- The finite check up to `n`. -/
def allOK (n : ℕ) : Bool := (List.range n).all fun q => decide (q ≤ 2) || checkGen q (yOf q)

lemma subgroup_eq_top_of_le_two {q : ℕ} [NeZero q] (hq : q ≤ 2) (H : Subgroup (ZMod q)ˣ) :
    H = ⊤ := by
  have hcard : Fintype.card (ZMod q)ˣ ≤ 1 := by
    rw [ZMod.card_units_eq_totient]
    interval_cases q <;> simp at *
  have : Subsingleton (ZMod q)ˣ := Fintype.card_le_one_iff_subsingleton.1 hcard
  exact eq_top_iff.2 fun a _ => (Subsingleton.elim a 1) ▸ H.one_mem

theorem bach_of_allOK {n : ℕ} (h : allOK n = true) (q : ℕ) [NeZero q] (hq : q < n)
    (H : Subgroup (ZMod q)ˣ) (hH : H ≠ ⊤) :
    ∃ a : (ZMod q)ˣ, a ∉ H ∧ ((a : ZMod q).val : ℝ) ≤ 5 * Real.log q ^ 2 := by
  have hq' := List.all_eq_true.1 h q (List.mem_range.2 hq)
  simp only [Bool.or_eq_true, decide_eq_true_eq] at hq'
  rcases hq' with hle | hchk
  · exact absurd (subgroup_eq_top_of_le_two hle H) hH
  have htop := closure_eq_top_of_checkGen q (yOf q) hchk
  by_contra hcon
  push Not at hcon
  apply hH
  rw [eq_top_iff, ← htop, Subgroup.closure_le]
  intro u hu
  by_contra huH
  have h1 := hcon u huH
  have h2 : ((u : ZMod q).val : ℝ) ≤ yOf q := by exact_mod_cast hu
  have h3 := yOf_le q (NeZero.ne q)
  linarith

end Ankeny
