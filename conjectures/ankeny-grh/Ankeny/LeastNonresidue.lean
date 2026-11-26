import Ankeny.Statement

/-!
# From subgroups to the least quadratic non-residue

For an odd prime `p` the squares form a proper subgroup of `(ZMod p)ˣ`: squaring is not
injective because `(-1)² = 1² ` and `-1 ≠ 1`. A unit outside it is a non-residue, and its
least residue is positive.
-/

namespace Ankeny

theorem leastNonresidue_of_bach' {c : ℝ} (h : BachSubgroupBound c) : LeastNonresidueBound c := by
  intro p hp hp2
  have : Fact p.Prime := ⟨hp⟩
  have : Fact (2 < p) := ⟨lt_of_le_of_ne hp.two_le (Ne.symm hp2)⟩
  let sq : (ZMod p)ˣ →* (ZMod p)ˣ := powMonoidHom 2
  have hH : sq.range ≠ ⊤ := by
    intro htop
    have hinj : Function.Injective sq :=
      Finite.injective_iff_surjective.2 (MonoidHom.range_eq_top.1 htop)
    have h1 : (-1 : (ZMod p)ˣ) = 1 := hinj (by simp [sq])
    exact ZMod.neg_one_ne_one (by simpa using congrArg Units.val h1)
  obtain ⟨a, haH, hle⟩ := h p sq.range hH
  refine ⟨(a : ZMod p).val, ?_, hle, ?_⟩
  · rw [Nat.pos_iff_ne_zero, Ne, ZMod.val_eq_zero]
    exact a.ne_zero
  · rintro ⟨r, hr⟩
    rw [ZMod.natCast_zmod_val] at hr
    have hr0 : r ≠ 0 := by
      rintro rfl
      simp at hr
    apply haH
    refine ⟨Units.mk0 r hr0, Units.ext ?_⟩
    simp [sq, hr, pow_two]

end Ankeny
