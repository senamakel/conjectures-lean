import BachCorollaries.Statement

/-!
# Small generators of `(ℤ/m)ˣ` from Bach's subgroup bound

If the units represented by positive integers `a ≤ c log² m` generated a proper subgroup `H`,
`Ankeny.BachSubgroupBound c` would give a unit `u ∉ H` of residue `≤ c log² m`; but `u` is one of
the generators. So they generate everything (Bach 1990, §6, with his `3` replaced by `c`).
-/

namespace BachCorollaries

/-- In `(ZMod 1)ˣ` (the trivial group) every subgroup is `⊤`. -/
theorem subgroup_eq_top_of_subsingleton {G : Type*} [Group G] [Subsingleton G]
    (H : Subgroup G) : H = ⊤ :=
  eq_top_iff.mpr fun u _ => Subsingleton.elim u 1 ▸ H.one_mem

/-- **Bach's generator theorem**, from Bach's subgroup bound with any constant `c`. -/
theorem generators_of_bach {c : ℝ} (h : Ankeny.BachSubgroupBound c) : GeneratorBound c := by
  intro m _
  by_contra hne
  obtain ⟨u, hu, huc⟩ := h m _ hne
  rcases Nat.lt_or_ge m 2 with hm | hm
  · have hm1 : m = 1 := by have := NeZero.ne m; omega
    subst hm1
    exact hne (subgroup_eq_top_of_subsingleton _)
  have : Nontrivial (ZMod m) := ZMod.nontrivial_iff.mpr (by omega)
  refine hu (Subgroup.subset_closure ⟨(u : ZMod m).val,
    Nat.pos_of_ne_zero ((ZMod.val_ne_zero _).mpr u.ne_zero), huc, ?_⟩)
  rw [ZMod.natCast_zmod_val]

end BachCorollaries
