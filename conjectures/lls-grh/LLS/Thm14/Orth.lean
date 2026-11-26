import Mathlib

/-!
# Orthogonality over the characters trivial on a subgroup

For a subgroup `H` of `G = (ℤ/qℤ)ˣ`, `LLS.Thm14.Htil H` is the finite set of Dirichlet characters
mod `q` that are `1` on `H` (LLS's `H̃`). With `m = |H̃|`:

* `LLS.Thm14.card_Htil_le`: `m ≤ [G : H]` (they inject into the characters of `G/H`);
* `LLS.Thm14.sum_Htil_unit`: `Σ_{χ ∈ H̃} χ(v) = m` if `v ∈ H` and `0` otherwise;
* `LLS.Thm14.sum_Htil_coset`: `Σ_{χ ∈ H̃} χ(a⁻¹) χ(n) = m · 1[n ∈ aH]` for `n ∈ ℕ`;
* `LLS.Thm14.re_sum_Htil_ne_one_ge`: `Re Σ_{χ ∈ H̃, χ ≠ 1} χ(n) ≥ −1`.
-/

namespace LLS.Thm14

open Finset
open scoped Classical

variable {q : ℕ} [NeZero q]

/-- The characters mod `q` trivial on `H`. -/
noncomputable def Htil (H : Subgroup (ZMod q)ˣ) : Finset (DirichletCharacter ℂ q) :=
  (Set.toFinite {χ : DirichletCharacter ℂ q | ∀ u ∈ H, χ (u : ZMod q) = 1}).toFinset

lemma mem_Htil {H : Subgroup (ZMod q)ˣ} {χ : DirichletCharacter ℂ q} :
    χ ∈ Htil H ↔ ∀ u ∈ H, χ (u : ZMod q) = 1 := by
  simp [Htil]

lemma one_mem_Htil (H : Subgroup (ZMod q)ˣ) : (1 : DirichletCharacter ℂ q) ∈ Htil H :=
  mem_Htil.2 fun u _ => by simp

lemma quot_finite (H : Subgroup (ZMod q)ˣ) : Finite ((ZMod q)ˣ ⧸ H) :=
  Finite.of_surjective _ (QuotientGroup.mk'_surjective H)

lemma quot_exp (H : Subgroup (ZMod q)ˣ) : NeZero (Monoid.exponent ((ZMod q)ˣ ⧸ H) : ℂ) := by
  have := quot_finite H
  exact ⟨Nat.cast_ne_zero.2 (Monoid.ExponentExists.exponent_ne_zero
    (Monoid.ExponentExists.of_finite (G := (ZMod q)ˣ ⧸ H)))⟩

/-- The character of `G/H` attached to `χ ∈ H̃`. -/
noncomputable def toQuot (H : Subgroup (ZMod q)ˣ) (χ : Htil H) : ((ZMod q)ˣ ⧸ H) →* ℂˣ :=
  QuotientGroup.lift H (MulChar.toUnitHom (χ : DirichletCharacter ℂ q)) (by
    intro u hu
    rw [MonoidHom.mem_ker]
    ext
    simpa [MulChar.coe_toUnitHom] using mem_Htil.1 χ.2 u hu)

lemma toQuot_injective (H : Subgroup (ZMod q)ˣ) : Function.Injective (toQuot H) := by
  intro χ ψ h
  apply Subtype.ext
  apply MulChar.ext
  intro u
  have := congrArg (fun φ : ((ZMod q)ˣ ⧸ H) →* ℂˣ => (φ (QuotientGroup.mk u) : ℂ)) h
  simpa [toQuot, MulChar.coe_toUnitHom] using this

theorem card_Htil_le (H : Subgroup (ZMod q)ˣ) : (Htil H).card ≤ H.index := by
  have := quot_finite H
  have := quot_exp H
  have hfin : Finite (((ZMod q)ˣ ⧸ H) →* ℂˣ) := by
    have h := CommGroup.card_monoidHom_of_hasEnoughRootsOfUnity ((ZMod q)ˣ ⧸ H) ℂ
    exact Nat.finite_of_card_ne_zero (by rw [h]; exact Nat.card_pos.ne')
  rw [← Nat.card_eq_finsetCard]
  calc Nat.card (Htil H) ≤ Nat.card (((ZMod q)ˣ ⧸ H) →* ℂˣ) :=
        Nat.card_le_card_of_injective _ (toQuot_injective H)
    _ = Nat.card ((ZMod q)ˣ ⧸ H) :=
        CommGroup.card_monoidHom_of_hasEnoughRootsOfUnity ((ZMod q)ˣ ⧸ H) ℂ
    _ = H.index := rfl

/-- A character trivial on `H` and not `1` at `v ∉ H`. -/
lemma exists_Htil_ne_one (H : Subgroup (ZMod q)ˣ) {v : (ZMod q)ˣ} (hv : v ∉ H) :
    ∃ χ ∈ Htil H, χ (v : ZMod q) ≠ 1 := by
  have := quot_finite H
  have := quot_exp H
  have ha : (QuotientGroup.mk v : (ZMod q)ˣ ⧸ H) ≠ 1 := by
    rwa [Ne, QuotientGroup.eq_one_iff]
  obtain ⟨ψ, hψ⟩ := CommGroup.exists_apply_ne_one_of_hasEnoughRootsOfUnity _ ℂ ha
  let φ : (ZMod q)ˣ →* ℂˣ := ψ.comp (QuotientGroup.mk' H)
  refine ⟨MulChar.ofUnitHom φ, mem_Htil.2 fun u hu => ?_, fun h => hψ ?_⟩
  · rw [MulChar.ofUnitHom_coe]
    have : (QuotientGroup.mk' H u : (ZMod q)ˣ ⧸ H) = 1 := (QuotientGroup.eq_one_iff u).2 hu
    show ((ψ (QuotientGroup.mk' H u) : ℂˣ) : ℂ) = 1
    rw [this, map_one, Units.val_one]
  · rw [MulChar.ofUnitHom_coe] at h
    exact Units.ext (by simpa [φ] using h)

theorem sum_Htil_unit (H : Subgroup (ZMod q)ˣ) (v : (ZMod q)ˣ) :
    ∑ χ ∈ Htil H, χ (v : ZMod q) = if v ∈ H then ((Htil H).card : ℂ) else 0 := by
  split_ifs with hv
  · rw [sum_congr rfl fun χ hχ => mem_Htil.1 hχ v hv]
    simp
  · obtain ⟨χ₁, h₁, hne⟩ := exists_Htil_ne_one H hv
    set S := ∑ χ ∈ Htil H, χ (v : ZMod q)
    have hS : S = χ₁ (v : ZMod q) * S := by
      rw [mul_sum]
      refine sum_nbij' (fun χ => χ₁⁻¹ * χ) (fun χ => χ₁ * χ) ?_ ?_ ?_ ?_ ?_
      · intro χ hχ
        refine mem_Htil.2 fun u hu => ?_
        rw [MulChar.mul_apply, MulChar.inv_apply_eq_inv', mem_Htil.1 h₁ u hu,
          mem_Htil.1 hχ u hu, inv_one, mul_one]
      · intro χ hχ
        refine mem_Htil.2 fun u hu => ?_
        rw [MulChar.mul_apply, mem_Htil.1 h₁ u hu, mem_Htil.1 hχ u hu, mul_one]
      · intro χ _; simp
      · intro χ _; simp
      · intro χ _
        simp only [MulChar.mul_apply, MulChar.inv_apply_eq_inv']
        have h0 : χ₁ (v : ZMod q) ≠ 0 := by rw [← MulChar.coe_toUnitHom]; exact Units.ne_zero _
        field_simp
    have h1 : (1 - χ₁ (v : ZMod q)) * S = 0 := by rw [sub_mul, one_mul, ← hS, sub_self]
    rcases mul_eq_zero.1 h1 with h | h
    · exact absurd (sub_eq_zero.1 h).symm hne
    · exact h

/-- The coset indicator: `Σ_{χ ∈ H̃} χ(a⁻¹) χ(n) = |H̃| · 1[(n, q) = 1, a⁻¹ n ∈ H]`. -/
theorem sum_Htil_coset (H : Subgroup (ZMod q)ˣ) (a : (ZMod q)ˣ) (n : ℕ) :
    ∑ χ ∈ Htil H, χ ((a⁻¹ : (ZMod q)ˣ) : ZMod q) * χ n
      = if h : n.Coprime q then
          (if a⁻¹ * ZMod.unitOfCoprime n h ∈ H then ((Htil H).card : ℂ) else 0)
        else 0 := by
  have key : ∀ hc : n.Coprime q, ∑ χ ∈ Htil H, χ ((a⁻¹ : (ZMod q)ˣ) : ZMod q) * χ n
      = ∑ χ ∈ Htil H, χ ((a⁻¹ * ZMod.unitOfCoprime n hc : (ZMod q)ˣ) : ZMod q) := fun hc =>
    sum_congr rfl fun χ _ => by rw [Units.val_mul, map_mul, ZMod.coe_unitOfCoprime]
  split_ifs with hc hm
  · rw [key hc, sum_Htil_unit H, if_pos hm]
  · rw [key hc, sum_Htil_unit H, if_neg hm]
  · refine sum_eq_zero fun χ _ => ?_
    have : ¬ IsUnit (n : ZMod q) := fun h => hc ((ZMod.isUnit_iff_coprime n q).1 h)
    rw [MulChar.map_nonunit χ this, mul_zero]

/-- `Re Σ_{χ ∈ H̃, χ ≠ 1} χ(n) ≥ −1`. -/
theorem re_sum_Htil_ne_one_ge (H : Subgroup (ZMod q)ˣ) (n : ℕ) :
    -1 ≤ (∑ χ ∈ (Htil H).erase 1, χ n).re := by
  have hsplit := Finset.add_sum_erase (Htil H) (fun χ : DirichletCharacter ℂ q => χ n)
    (one_mem_Htil H)
  have htot := sum_Htil_coset H 1 n
  simp only [inv_one, Units.val_one, map_one, one_mul] at htot
  have hre : (∑ χ ∈ Htil H, χ n).re ≥ 0 := by
    rw [htot]
    split_ifs <;> simp
  have h1 : ((1 : DirichletCharacter ℂ q) n).re ≤ 1 := by
    have := Complex.re_le_norm ((1 : DirichletCharacter ℂ q) n)
    have := DirichletCharacter.norm_le_one (1 : DirichletCharacter ℂ q) n
    linarith
  rw [← hsplit, Complex.add_re] at hre
  linarith

end LLS.Thm14
