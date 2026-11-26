import BachSharp.Basic

/-!
# The constant `2 / log² 3` cannot be lowered

For `m = 3` the only unit other than `1` is `2`, and `2 = (2 / log² 3) log² 3`: with any
`c < 2 / log² 3` the trivial subgroup misses no unit `≤ c log² 3`, and the positive integers
`≤ c log² 3 < 2` give only the class `1`.
-/

namespace BachSharp

lemma units_three_val (a : (ZMod 3)ˣ) (ha : a ≠ 1) : (a : ZMod 3).val = 2 := by
  revert a; decide

lemma bot_ne_top_three : (⊥ : Subgroup (ZMod 3)ˣ) ≠ ⊤ := by
  intro h
  have : (-1 : (ZMod 3)ˣ) ∈ (⊥ : Subgroup (ZMod 3)ˣ) := h ▸ Subgroup.mem_top _
  rw [Subgroup.mem_bot] at this
  exact absurd this (by decide)

/-- **Optimality of `2 / log² 3`** (tier D). -/
theorem sharpOptimal : SharpOptimal := by
  intro c hc
  have hl := log_three_pos
  have h2 : c * Real.log 3 ^ 2 < 2 := by
    rw [← sharpConst_mul_log_three_sq]
    exact mul_lt_mul_of_pos_right hc (by positivity)
  constructor
  · intro hB
    obtain ⟨a, ha, hle⟩ := hB 3 ⊥ bot_ne_top_three
    have ha1 : a ≠ 1 := by simpa [Subgroup.mem_bot] using ha
    rw [units_three_val a ha1] at hle
    push_cast at hle
    linarith
  · intro hG
    have h := hG 3
    have hS : {u : (ZMod 3)ˣ | ∃ a : ℕ, 0 < a ∧ (a : ℝ) ≤ c * Real.log (3 : ℕ) ^ 2 ∧
        (u : ZMod 3) = a} ⊆ (⊥ : Subgroup (ZMod 3)ˣ) := by
      rintro u ⟨a, ha0, hac, hu⟩
      have ha2 : (a : ℝ) < 2 := by push_cast at hac; linarith
      have ha2' : a < 2 := by exact_mod_cast ha2
      have : a = 1 := by omega
      subst this
      rw [SetLike.mem_coe, Subgroup.mem_bot]
      ext
      simpa using hu
    have : (⊤ : Subgroup (ZMod 3)ˣ) ≤ ⊥ := by
      rw [← h, Subgroup.closure_le]
      exact hS
    exact bot_ne_top_three (le_antisymm bot_le this)

end BachSharp
