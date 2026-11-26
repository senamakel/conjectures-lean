import Mathlib

/-!
# A non-trivial Dirichlet character trivial on a proper subgroup

If `H` is a proper subgroup of `(ZMod q)ˣ`, the quotient `(ZMod q)ˣ ⧸ H` is a non-trivial finite
abelian group, so it has a non-trivial character. Pulled back to `(ZMod q)ˣ` it is a Dirichlet
character `χ ≠ 1` with `χ u = 1` for every `u ∈ H`.
-/

namespace Ankeny

open scoped Classical

theorem exists_dirichletCharacter_trivial_on {q : ℕ} [NeZero q] (H : Subgroup (ZMod q)ˣ)
    (hH : H ≠ ⊤) :
    ∃ χ : DirichletCharacter ℂ q, χ ≠ 1 ∧ ∀ u ∈ H, χ (u : ZMod q) = 1 := by
  obtain ⟨a, haH⟩ : ∃ a, a ∉ H := by
    by_contra h
    exact hH (eq_top_iff.2 fun a _ => not_not.1 fun ha => h ⟨a, ha⟩)
  set G := (ZMod q)ˣ ⧸ H
  have ha : (QuotientGroup.mk a : G) ≠ 1 := by
    rwa [Ne, QuotientGroup.eq_one_iff]
  have : Finite G := Finite.of_surjective _ (QuotientGroup.mk'_surjective H)
  have hexp : NeZero (Monoid.exponent G : ℂ) :=
    ⟨Nat.cast_ne_zero.2 (Monoid.ExponentExists.exponent_ne_zero (Monoid.ExponentExists.of_finite (G := G)))⟩
  obtain ⟨ψ, hψ⟩ := CommGroup.exists_apply_ne_one_of_hasEnoughRootsOfUnity G ℂ ha
  let φ : (ZMod q)ˣ →* ℂˣ := ψ.comp (QuotientGroup.mk' H)
  refine ⟨MulChar.ofUnitHom φ, fun h => ?_, fun u hu => ?_⟩
  · apply hψ
    have h1 := congrArg (fun χ : DirichletCharacter ℂ q => χ (a : ZMod q)) h
    simp only [MulChar.ofUnitHom_coe, MulChar.one_apply_coe] at h1
    exact (Units.ext (by simpa using h1) : φ a = 1)
  · rw [MulChar.ofUnitHom_coe]
    have : (QuotientGroup.mk' H u : G) = 1 := (QuotientGroup.eq_one_iff u).2 hu
    simp [φ, this]

end Ankeny
