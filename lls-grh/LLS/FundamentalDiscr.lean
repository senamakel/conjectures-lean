import Mathlib

/-!
# The discriminant of a quadratic field is a fundamental discriminant

`discr_isFundamentalDiscr`: for every number field `K` of degree `2`, `NumberField.discr K` is a
fundamental discriminant (`Int.IsFundamentalDiscr`): it is `≡ 1 (mod 4)` and squarefree, or it
is `4m` with `m` squarefree and `m ≡ 2, 3 (mod 4)`. This contains Stickelberger's congruence
`discr K ≡ 0, 1 (mod 4)` for quadratic fields.

Proof, from Mathlib's quadratic algebras:
1. `K ≃ₐ[ℚ] ℚ[ω]/(ω² = a + bω)` for some `a, b : ℚ`
   (`Algebra.IsQuadraticExtension.exists_algEquiv_quadraticAlgebra`), and that is isomorphic to
   `ℚ(√d)` for a squarefree integer `d` (`QuadraticAlgebra.Rat.exists_squarefree_algEquiv`).
2. `D := d` if `d ≡ 1 (mod 4)`, else `D := 4d`, is a fundamental discriminant, and
   `ℚ(√d) ≃ₐ[ℚ] QuadraticAlgebra ℚ (D/4) (D%4)` (the discriminants differ by a square).
3. `QuadraticAlgebra ℤ (D/4) (D%4)` is the integral closure of `ℤ` in
   `QuadraticAlgebra ℚ (D/4) (D%4)` because `D` is fundamental
   (`QuadraticAlgebra.Int.algEquivIntegralClosure`), so it is isomorphic to `𝓞 K`, and the
   discriminant of its basis `{1, ω}` is `D` (`Algebra.discr_quadraticAlgebra`).
-/

namespace LLS

open NumberField Module QuadraticAlgebra

/-- `D := d` for `d ≡ 1 (mod 4)` and `4d` otherwise is a fundamental discriminant when `d` is
squarefree. -/
lemma isFundamentalDiscr_of_squarefree {d : ℤ} (hd : Squarefree d) :
    Int.IsFundamentalDiscr (if d % 4 = 1 then d else 4 * d) := by
  split_ifs with h
  · exact Int.isFundamentalDiscr_iff_squarefree.2 (Or.inl ⟨h, hd⟩)
  · refine Int.isFundamentalDiscr_four_mul.2 ⟨hd, ?_⟩
    have h4 : ¬ (4 : ℤ) ∣ d := fun h4 => by
      obtain ⟨k, rfl⟩ := h4
      have := hd 2 ⟨k, by ring⟩
      exact absurd (Int.isUnit_iff.1 this) (by omega)
    omega

/-- **The discriminant of a quadratic field is a fundamental discriminant.** -/
theorem discr_isFundamentalDiscr (K : Type*) [Field K] [NumberField K] (h2 : finrank ℚ K = 2) :
    Int.IsFundamentalDiscr (discr K) := by
  have : Algebra.IsQuadraticExtension ℚ K := ⟨h2⟩
  obtain ⟨a, b, ⟨e⟩⟩ :=
    Algebra.IsQuadraticExtension.exists_algEquiv_quadraticAlgebra (R := ℚ) (A := K)
  have hab : QuadraticAlgebra.discr a b ≠ 0 := by
    intro h0
    have hF : IsField (QuadraticAlgebra ℚ a b) :=
      MulEquiv.isField (Field.toIsField K) e.symm.toMulEquiv
    rw [isField_iff_not_isSquare_discr] at hF
    exact hF ⟨0, by simp [h0]⟩
  obtain ⟨d, hd, ⟨e'⟩⟩ := QuadraticAlgebra.Rat.exists_squarefree_algEquiv hab
  set D : ℤ := if d % 4 = 1 then d else 4 * d with hDdef
  have hD : Int.IsFundamentalDiscr D := isFundamentalDiscr_of_squarefree hd
  have hD4 := hD.emod_four_eq_zero_or_one
  -- `QuadraticAlgebra ℚ (D/4) (D%4) ≃ₐ[ℚ] ℚ(√d)`
  have hiso : Nonempty (QuadraticAlgebra ℚ ((D / 4 : ℤ) : ℚ) ((D % 4 : ℤ) : ℚ)
      ≃ₐ[ℚ] QuadraticAlgebra ℚ (d : ℚ) 0) := by
    rw [nonempty_algEquiv_iff_of_invertible_two]
    have h1 : QuadraticAlgebra.discr ((D / 4 : ℤ) : ℚ) ((D % 4 : ℤ) : ℚ) = (D : ℚ) := by
      rw [discr_intCast, discr_ediv_emod hD4]
    have h2' : QuadraticAlgebra.discr (d : ℚ) (0 : ℚ) = 4 * d := by
      rw [discr_def]; ring
    rw [h1, h2']
    by_cases h : d % 4 = 1
    · refine ⟨Units.mk0 (1 / 2) (by norm_num), ?_⟩
      simp only [hDdef, h, ↓reduceIte, Units.val_mk0]
      ring
    · refine ⟨1, ?_⟩
      simp only [hDdef, h, ↓reduceIte, Units.val_one]
      push_cast
      ring
  obtain ⟨f⟩ := hiso
  let g := (f.trans (e'.symm.trans e.symm)).restrictScalars ℤ
  -- `𝓞 K ≃ₐ[ℤ] QuadraticAlgebra ℤ (D/4) (D%4)`
  let φ : QuadraticAlgebra ℤ (D / 4) (D % 4) ≃ₐ[ℤ] 𝓞 K :=
    (Int.algEquivIntegralClosure (a := D / 4) (b := D % 4)
      (by rwa [discr_ediv_emod hD4])).trans g.mapIntegralClosure
  let B : Basis (Fin 2) ℤ (𝓞 K) := (QuadraticAlgebra.basis (D / 4) (D % 4)).map φ.toLinearEquiv
  rw [← NumberField.discr_eq_discr K B]
  have : (B : Fin 2 → 𝓞 K) = φ ∘ (QuadraticAlgebra.basis (D / 4) (D % 4)) := by
    ext i : 1
    simp [B]
  rw [this, ← Algebra.discr_eq_discr_of_algEquiv, Algebra.discr_quadraticAlgebra,
    discr_ediv_emod hD4]
  exact hD

end LLS
