import BachSharp.Statement
import Ankeny.Finite

/-!
# Basic facts about the sharp constant

`sharpConst * log² 3 = 2`, `1.657 ≤ sharpConst`, and two ways from a bound at one modulus to the
subgroup and generator forms.
-/

namespace BachSharp

lemma log_three_pos : 0 < Real.log 3 := Real.log_pos (by norm_num)

lemma sharpConst_mul_log_three_sq : sharpConst * Real.log 3 ^ 2 = 2 := by
  have := log_three_pos
  unfold sharpConst
  field_simp

/-- `1.657 ≤ 2 / log² 3` (from `log 3 < 1.0986122888`). -/
lemma c1657_le_sharpConst : (1657 / 1000 : ℝ) ≤ sharpConst := by
  have h := Real.log_three_lt_d9
  have h0 := log_three_pos
  unfold sharpConst
  rw [le_div_iff₀ (by positivity)]
  nlinarith

/-- If the units of residue `≤ y` generate, every proper subgroup misses one of them. -/
lemma exists_not_mem_of_closure {q y : ℕ} [NeZero q]
    (h : Subgroup.closure (Ankeny.Checker.smallUnits q y) = ⊤) (H : Subgroup (ZMod q)ˣ)
    (hH : H ≠ ⊤) : ∃ a : (ZMod q)ˣ, a ∉ H ∧ ((a : ZMod q).val : ℝ) ≤ y := by
  by_contra hcon
  push Not at hcon
  apply hH
  rw [eq_top_iff, ← h, Subgroup.closure_le]
  intro u hu
  by_contra huH
  have h1 := hcon u huH
  have h2 : ((u : ZMod q).val : ℝ) ≤ y := by exact_mod_cast hu
  linarith

/-- The subgroup bound at one modulus gives the generator bound there
(`BachCorollaries.generators_of_bach`, one modulus at a time). -/
lemma closure_eq_top_of_subgroup_bound {c : ℝ} (m : ℕ) [NeZero m]
    (h : ∀ H : Subgroup (ZMod m)ˣ, H ≠ ⊤ →
      ∃ a : (ZMod m)ˣ, a ∉ H ∧ ((a : ZMod m).val : ℝ) ≤ c * Real.log m ^ 2) :
    Subgroup.closure {u : (ZMod m)ˣ |
      ∃ a : ℕ, 0 < a ∧ (a : ℝ) ≤ c * Real.log m ^ 2 ∧ (u : ZMod m) = a} = ⊤ := by
  by_contra hne
  obtain ⟨u, hu, huc⟩ := h _ hne
  rcases Nat.lt_or_ge m 2 with hm | hm
  · have hm1 : m = 1 := by have := NeZero.ne m; omega
    subst hm1
    exact hne (eq_top_iff.mpr fun v _ => Subsingleton.elim v 1 ▸ Subgroup.one_mem _)
  have : Nontrivial (ZMod m) := ZMod.nontrivial_iff.mpr (by omega)
  refine hu (Subgroup.subset_closure ⟨(u : ZMod m).val,
    Nat.pos_of_ne_zero ((ZMod.val_ne_zero _).mpr u.ne_zero), huc, ?_⟩)
  rw [ZMod.natCast_zmod_val]

end BachSharp
