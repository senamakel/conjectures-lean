import BachSharp.Small
import BachSharp.Large
import BachSharp.Optimal
import LLS.Bach2.Main2

/-!
# Bach's sharp constant `2 / log² 3`: what is proved

* `sharpOptimal : SharpOptimal` (D): no smaller constant works.
* `sharp_small` (D): the sharp bound for every `m < 2^17`.
* `sharp_large_of_GRH` (C): the sharp bound for every `m ≥ 5 · 2^49` (with constant `1.657`).
* `sharp_outside_gap_of_GRH`, `generators_outside_gap_of_GRH` (C): the two together, in subgroup
  and generator form, for every `m` outside the gap `2^17 ≤ m < 5 · 2^49`.
* `sharp_of_GRH_of_gap` (C): GRH and the bound on the gap give `SharpSubgroupBound` and
  `SharpGeneratorBound`. On the gap the constant `2` holds (lls-grh's `LLS.bach2_of_GRH`).
-/

namespace BachSharp

open Erdos985 (DirichletLNonvanishingRightOfHalf)

/-- The sharp bound on the moduli not covered here, `2^17 ≤ m < 5 · 2^49`. -/
def SharpGap : Prop :=
  ∀ (q : ℕ) [NeZero q], 2 ^ 17 ≤ q → q < 5 * 2 ^ 49 → ∀ H : Subgroup (ZMod q)ˣ, H ≠ ⊤ →
    ∃ a : (ZMod q)ˣ, a ∉ H ∧ ((a : ZMod q).val : ℝ) ≤ sharpConst * Real.log q ^ 2

/-- **The sharp subgroup bound outside the gap, under GRH.** For every modulus `q < 2^17` or
`q ≥ 5 · 2^49`, every proper subgroup of `(ZMod q)ˣ` misses a unit of residue
`≤ (2 / log² 3) log² q`. -/
theorem sharp_outside_gap_of_GRH (hGRH : DirichletLNonvanishingRightOfHalf) (q : ℕ) [NeZero q]
    (hq : q < 2 ^ 17 ∨ 5 * 2 ^ 49 ≤ q) (H : Subgroup (ZMod q)ˣ) (hH : H ≠ ⊤) :
    ∃ a : (ZMod q)ˣ, a ∉ H ∧ ((a : ZMod q).val : ℝ) ≤ sharpConst * Real.log q ^ 2 := by
  rcases hq with h | h
  · exact sharp_small q h H hH
  · exact sharp_large_of_GRH hGRH q h H hH

/-- **The sharp generator bound outside the gap, under GRH.** -/
theorem generators_outside_gap_of_GRH (hGRH : DirichletLNonvanishingRightOfHalf) (m : ℕ)
    [NeZero m] (hm : m < 2 ^ 17 ∨ 5 * 2 ^ 49 ≤ m) :
    Subgroup.closure {u : (ZMod m)ˣ |
      ∃ a : ℕ, 0 < a ∧ (a : ℝ) ≤ sharpConst * Real.log m ^ 2 ∧ (u : ZMod m) = a} = ⊤ :=
  closure_eq_top_of_subgroup_bound m (sharp_outside_gap_of_GRH hGRH m hm)

/-- **Reduction to the gap.** GRH and the sharp bound for `2^17 ≤ m < 5 · 2^49` give the sharp
bound for every modulus, in both forms. -/
theorem sharp_of_GRH_of_gap (hGRH : DirichletLNonvanishingRightOfHalf) (hgap : SharpGap) :
    SharpSubgroupBound ∧ SharpGeneratorBound := by
  have hB : SharpSubgroupBound := by
    intro q _ H hH
    rcases Nat.lt_or_ge q (2 ^ 17) with h | h
    · exact sharp_small q h H hH
    rcases Nat.lt_or_ge q (5 * 2 ^ 49) with h' | h'
    · exact hgap q h h' H hH
    · exact sharp_large_of_GRH hGRH q h' H hH
  exact ⟨hB, fun m _ => closure_eq_top_of_subgroup_bound m (hB m)⟩

/-- **Everything at once, under GRH.** Constant `2` for every modulus (lls-grh), constant
`2 / log² 3` outside the gap, and `2 / log² 3` cannot be lowered. -/
theorem bach_sharp_of_GRH (hGRH : DirichletLNonvanishingRightOfHalf) :
    Ankeny.BachSubgroupBound 2 ∧
    (∀ (q : ℕ) [NeZero q], (q < 2 ^ 17 ∨ 5 * 2 ^ 49 ≤ q) → ∀ H : Subgroup (ZMod q)ˣ, H ≠ ⊤ →
      ∃ a : (ZMod q)ˣ, a ∉ H ∧ ((a : ZMod q).val : ℝ) ≤ sharpConst * Real.log q ^ 2) ∧
    SharpOptimal :=
  ⟨LLS.bach2_of_GRH hGRH, fun q _ hq H hH => sharp_outside_gap_of_GRH hGRH q hq H hH,
    sharpOptimal⟩

end BachSharp
