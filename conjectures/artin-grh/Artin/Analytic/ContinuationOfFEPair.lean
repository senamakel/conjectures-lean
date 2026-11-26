import Artin.Analytic.Continuation

/-!
# `DedekindContinuation` from a functional-equation pair

Mathlib's `WeakFEPair` packages a pair of functions `f`, `g` on `(0, ∞)` with
`f(1/x) = ε x^k g(x)` and rapid decay of `f - f₀`, `g - g₀` at infinity. Its Mellin transform
`Λ = Λ₀ - f₀/s - ε g₀/(k - s)` has an entire part `Λ₀` (`WeakFEPair.differentiable_Λ₀`). Hecke's
proof of the continuation of `ζ_K` (and Tate's adelic proof) produce `Λ_K` in exactly this form,
with `k = ε = 1`.

This file proves, from Mathlib alone:

* `exists_norm_Λ₀_le`: `Λ₀` is bounded on every vertical strip `a ≤ Re s ≤ b` (the Mellin integral
  of `f_modif` converges absolutely for every `s`, and `t^{σ-1} ≤ t^{a-1} + t^{b-1}`);
* `dedekindContinuation_of_weakFEPair`: if a completed zeta function `L` satisfies
  `L(s) = c |d_K|^{s/2} Λ(s)` off `{0, 1}`, `L(1 - s) = L(s)`, and `L = γ_K Z` on `Re s > 0` for some
  `Z` with `IsDedekindZeta K Z`, then `DedekindContinuation K` holds. The strip bound, which the
  riemann-hypothesis repository does not state, is the first item.

`Unconditional/ArtinUnconditional.lean` feeds this the Tate-thesis construction of
leanprover-community/riemann-hypothesis. Nothing here imports that repository.
-/

namespace Artin.Analytic

open Complex MeasureTheory Set NumberField ArtinPrimitiveRootsConjecture

/-- The entire part `Λ₀` of a weak FE-pair is bounded on every vertical strip `a ≤ Re s ≤ b`. -/
theorem exists_norm_Λ₀_le (P : WeakFEPair ℂ) (a b : ℝ) :
    ∃ C : ℝ, ∀ s : ℂ, a ≤ s.re → s.re ≤ b → ‖P.Λ₀ s‖ ≤ C := by
  have hP := P.isStrongFEPair_toStrongFEPair
  have ha : MellinConvergent P.f_modif (a : ℂ) := (hP.hasMellin (a : ℂ)).1
  have hb : MellinConvergent P.f_modif (b : ℂ) := (hP.hasMellin (b : ℂ)).1
  refine ⟨∫ t in Ioi (0 : ℝ), (‖(t : ℂ) ^ ((a : ℂ) - 1) • P.f_modif t‖ +
      ‖(t : ℂ) ^ ((b : ℂ) - 1) • P.f_modif t‖), fun s hsa hsb => ?_⟩
  have hs : MellinConvergent P.f_modif s := (hP.hasMellin s).1
  calc ‖P.Λ₀ s‖ = ‖∫ t in Ioi (0 : ℝ), (t : ℂ) ^ (s - 1) • P.f_modif t‖ := rfl
    _ ≤ ∫ t in Ioi (0 : ℝ), ‖(t : ℂ) ^ (s - 1) • P.f_modif t‖ :=
      norm_integral_le_integral_norm _
    _ ≤ _ := by
      refine setIntegral_mono_on hs.norm (ha.norm.add hb.norm) measurableSet_Ioi
        fun t (ht : 0 < t) => ?_
      simp only [norm_smul, norm_cpow_eq_rpow_re_of_pos ht, sub_re, one_re, ofReal_re]
      rw [← add_mul]
      refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
      rcases le_total t 1 with h | h
      · have := Real.rpow_le_rpow_of_exponent_ge ht h (by linarith : a - 1 ≤ s.re - 1)
        linarith [Real.rpow_nonneg ht.le (b - 1)]
      · have := Real.rpow_le_rpow_of_exponent_le h (by linarith : s.re - 1 ≤ b - 1)
        linarith [Real.rpow_nonneg ht.le (a - 1)]

lemma one_le_abs_discr (K : Type*) [Field K] [NumberField K] : 1 ≤ |(discr K : ℝ)| := by
  have h := Int.one_le_abs (discr_ne_zero K)
  exact_mod_cast h

/-- **Hecke's continuation from an FE-pair.** A completed zeta function of `K` written as
`c |d_K|^{s/2} Λ_P(s)` for a weak FE-pair `P` with `k = ε = 1`, with the functional equation
`L(1 - s) = L(s)` and agreeing with `γ_K Z` on `Re s > 0` for a continuation `Z` of `ζ_K`, gives
`DedekindContinuation K`. The entire function is
`ξ(s) = c |d_K|^{s/2} (s (s - 1) Λ₀(s) - (s - 1) f₀ + s g₀)`. -/
theorem dedekindContinuation_of_weakFEPair (K : Type*) [Field K] [NumberField K]
    (P : WeakFEPair ℂ) (hk : P.k = 1) (hε : P.ε = 1) (c : ℂ) (L Z : ℂ → ℂ)
    (hL : ∀ s : ℂ, s ≠ 0 → s ≠ 1 →
      L s = c * (((|(discr K : ℝ)| : ℝ)) : ℂ) ^ (s / 2) * P.Λ s)
    (hFE : ∀ s : ℂ, s ≠ 0 → s ≠ 1 → L (1 - s) = L s)
    (hZ : IsDedekindZeta K Z)
    (hLZ : ∀ s : ℂ, 0 < s.re → s ≠ 1 → completedOf K Z s = L s) :
    DedekindContinuation K := by
  set D : ℝ := |(discr K : ℝ)| with hDdef
  have hD1 : 1 ≤ D := one_le_abs_discr K
  have hD0 : 0 < D := by linarith
  have hDc : (D : ℂ) ≠ 0 := ofReal_ne_zero.2 hD0.ne'
  let ξ : ℂ → ℂ := fun s =>
    c * (D : ℂ) ^ (s / 2) * (s * (s - 1) * P.Λ₀ s - (s - 1) * P.f₀ + s * P.g₀)
  have hξL : ∀ s : ℂ, s ≠ 0 → s ≠ 1 → ξ s = s * (s - 1) * L s := by
    intro s h0 h1
    have h1' : (1 : ℂ) - s ≠ 0 := sub_ne_zero.2 (Ne.symm h1)
    have h1'' : s - 1 ≠ 0 := sub_ne_zero.2 h1
    rw [hL s h0 h1]
    simp only [ξ, WeakFEPair.Λ, hk, hε, smul_eq_mul, ofReal_one]
    field_simp
    ring
  have hdiff : Differentiable ℂ ξ := by
    have hc : Differentiable ℂ fun s : ℂ => (D : ℂ) ^ (s / 2) :=
      (differentiable_id.div_const 2).const_cpow (Or.inl hDc)
    have hΛ := P.differentiable_Λ₀
    have hid : Differentiable ℂ fun s : ℂ => s := differentiable_id
    exact (differentiable_const c).mul hc |>.mul
      (((hid.mul (hid.sub_const 1)).mul hΛ |>.sub
        ((hid.sub_const 1).mul_const _)).add (hid.mul_const _))
  refine ⟨ContinuationData.mk Z hZ ξ hdiff ?_ ?_ ?_⟩
  · intro s hs h1
    have h0 : s ≠ 0 := by rintro rfl; simp at hs
    rw [hξL s h0 h1, hLZ s hs h1]
  · intro s
    have hdense : Dense (({0, 1} : Set ℂ)ᶜ) :=
      ((Set.toFinite _).countable).dense_compl ℂ
    have hcont : Continuous fun s : ℂ => ξ (1 - s) :=
      hdiff.continuous.comp (continuous_const.sub continuous_id)
    refine congrFun (Continuous.ext_on hdense hcont hdiff.continuous fun z hz => ?_) s
    simp only [mem_compl_iff, mem_insert_iff, mem_singleton_iff, not_or] at hz
    obtain ⟨h0, h1⟩ := hz
    have h0' : (1 : ℂ) - z ≠ 0 := sub_ne_zero.2 (Ne.symm h1)
    have h1' : (1 : ℂ) - z ≠ 1 := by intro h; apply h0; linear_combination -h
    show ξ (1 - z) = ξ z
    rw [hξL _ h0' h1', hξL z h0 h1, hFE z h0 h1]
    ring
  · obtain ⟨C, hC⟩ := exists_norm_Λ₀_le P (1 / 2) 2
    refine ⟨‖c‖ * D * (|C| + ‖P.f₀‖ + ‖P.g₀‖), fun s hs1 hs2 => ?_⟩
    have hcp : ‖(D : ℂ) ^ (s / 2)‖ ≤ D := by
      rw [norm_cpow_eq_rpow_re_of_pos hD0]
      calc D ^ (s / 2).re ≤ D ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le hD1 (by simp; linarith)
        _ = D := Real.rpow_one D
    have hΛ : ‖P.Λ₀ s‖ ≤ |C| := (hC s hs1 hs2).trans (le_abs_self C)
    set r := ‖s‖
    have hr : 0 ≤ r := norm_nonneg s
    have hs1' : ‖s - 1‖ ≤ 1 + r := by
      calc ‖s - 1‖ ≤ ‖s‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
        _ = 1 + r := by simp [r]; ring
    have hinner : ‖s * (s - 1) * P.Λ₀ s - (s - 1) * P.f₀ + s * P.g₀‖ ≤
        (|C| + ‖P.f₀‖ + ‖P.g₀‖) * (1 + r) ^ 2 := by
      have e1 : ‖s * (s - 1) * P.Λ₀ s‖ ≤ (1 + r) ^ 2 * |C| := by
        rw [norm_mul, norm_mul]
        have : ‖s‖ * ‖s - 1‖ ≤ (1 + r) ^ 2 := by
          calc ‖s‖ * ‖s - 1‖ ≤ (1 + r) * (1 + r) :=
                mul_le_mul (by simp [r]) hs1' (norm_nonneg _) (by linarith)
            _ = (1 + r) ^ 2 := by ring
        exact mul_le_mul this hΛ (norm_nonneg _) (by positivity)
      have e2 : ‖(s - 1) * P.f₀‖ ≤ (1 + r) ^ 2 * ‖P.f₀‖ := by
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_right (hs1'.trans (by nlinarith)) (norm_nonneg _)
      have e3 : ‖s * P.g₀‖ ≤ (1 + r) ^ 2 * ‖P.g₀‖ := by
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_right (by nlinarith) (norm_nonneg _)
      calc _ ≤ ‖s * (s - 1) * P.Λ₀ s - (s - 1) * P.f₀‖ + ‖s * P.g₀‖ := norm_add_le _ _
        _ ≤ ‖s * (s - 1) * P.Λ₀ s‖ + ‖(s - 1) * P.f₀‖ + ‖s * P.g₀‖ := by
          gcongr; exact norm_sub_le _ _
        _ ≤ _ := by nlinarith
    show ‖c * (D : ℂ) ^ (s / 2) * (s * (s - 1) * P.Λ₀ s - (s - 1) * P.f₀ + s * P.g₀)‖ ≤ _
    rw [norm_mul, norm_mul]
    calc ‖c‖ * ‖(D : ℂ) ^ (s / 2)‖ * ‖s * (s - 1) * P.Λ₀ s - (s - 1) * P.f₀ + s * P.g₀‖
        ≤ ‖c‖ * D * ((|C| + ‖P.f₀‖ + ‖P.g₀‖) * (1 + r) ^ 2) := by
          gcongr
      _ = _ := by ring

end Artin.Analytic
