import Mathlib

namespace BachSharp

/-- Frattini-type criterion for finite abelian groups: if `H` together with the `ℓ`-th powers
generates `G` for every prime `ℓ`, then `H = G`. -/
theorem frattini_top {G : Type*} [CommGroup G] [Finite G] (H : Subgroup G)
    (h : ∀ ℓ : ℕ, ℓ.Prime → H ⊔ (powMonoidHom ℓ : G →* G).range = ⊤) : H = ⊤ := by
  by_contra hne
  have hnt : Nontrivial (G ⧸ H) := by
    rw [← not_subsingleton_iff_nontrivial]
    intro hs
    apply hne
    ext g
    simp only [Subgroup.mem_top, iff_true]
    have := hs.elim (g : G ⧸ H) 1
    exact (QuotientGroup.eq_one_iff g).mp this
  haveI := Fintype.ofFinite (G ⧸ H)
  have hc : Nat.card (G ⧸ H) ≠ 1 := by
    intro h1
    exact (not_subsingleton _) (Nat.card_eq_one_iff_unique.mp h1).1
  obtain ⟨ℓ, hℓ, hdvd⟩ := Nat.exists_prime_and_dvd hc
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := G ⧸ H) ℓ hdvd
  have hsurj : Function.Surjective (fun q : G ⧸ H => q ^ ℓ) := by
    intro q
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
    have hg : g ∈ H ⊔ (powMonoidHom ℓ : G →* G).range := by rw [h ℓ hℓ]; trivial
    obtain ⟨a, ha, b, ⟨c, rfl⟩, rfl⟩ := Subgroup.mem_sup.mp hg
    refine ⟨(c : G ⧸ H), ?_⟩
    simp only [powMonoidHom_apply]
    rw [QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff a).mpr ha, one_mul]
    rfl
  have hinj := Finite.injective_iff_surjective.mpr hsurj
  have h1 : x ^ ℓ = (1 : G ⧸ H) ^ ℓ := by rw [one_pow, ← hx]; exact pow_orderOf_eq_one x
  have := hinj h1
  rw [this, orderOf_one] at hx
  exact hℓ.one_lt.ne hx

/-- CRT bound on `ℓ`-torsion of unit groups. -/
theorem card_torsion_units_mul_le (m n ℓ : ℕ) (hmn : m.Coprime n) :
    Nat.card {u : (ZMod (m * n))ˣ // u ^ ℓ = 1} ≤
      Nat.card {u : (ZMod m)ˣ // u ^ ℓ = 1} * Nat.card {u : (ZMod n)ˣ // u ^ ℓ = 1} := by
  classical
  let e : (ZMod (m * n))ˣ ≃* (ZMod m)ˣ × (ZMod n)ˣ :=
    (Units.mapEquiv (ZMod.chineseRemainder hmn).toMulEquiv).trans MulEquiv.prodUnits
  let f : {u : (ZMod (m * n))ˣ // u ^ ℓ = 1} →
      {u : (ZMod m)ˣ // u ^ ℓ = 1} × {u : (ZMod n)ˣ // u ^ ℓ = 1} := fun u =>
    (⟨(e u.1).1, by
      have := congrArg Prod.fst (show (e u.1) ^ ℓ = 1 by rw [← map_pow, u.2, map_one])
      simpa using this⟩,
     ⟨(e u.1).2, by
      have := congrArg Prod.snd (show (e u.1) ^ ℓ = 1 by rw [← map_pow, u.2, map_one])
      simpa using this⟩)
  have hf : Function.Injective f := by
    intro u v huv
    simp only [f, Prod.mk.injEq, Subtype.mk.injEq] at huv
    apply Subtype.ext
    apply e.injective
    exact Prod.ext huv.1 huv.2
  rw [← Nat.card_prod]
  by_cases hm : m = 0
  · subst hm
    have hn : n = 1 := by simpa using hmn
    subst hn
    haveI : Finite {u : (ZMod 0)ˣ // u ^ ℓ = 1} := Subtype.finite
    haveI : Finite {u : (ZMod 1)ˣ // u ^ ℓ = 1} := Subtype.finite
    exact Nat.card_le_card_of_injective f hf
  by_cases hn : n = 0
  · subst hn
    have hm1 : m = 1 := by simpa using hmn
    subst hm1
    haveI : Finite {u : (ZMod 0)ˣ // u ^ ℓ = 1} := Subtype.finite
    haveI : Finite {u : (ZMod 1)ˣ // u ^ ℓ = 1} := Subtype.finite
    exact Nat.card_le_card_of_injective f hf
  haveI : NeZero m := ⟨hm⟩
  haveI : NeZero n := ⟨hn⟩
  exact Nat.card_le_card_of_injective f hf

end BachSharp
