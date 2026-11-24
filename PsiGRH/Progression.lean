import PsiGRH.Character

/-!
# Primes in arithmetic progressions (Montgomery–Vaughan (13.22), (13.23))

Orthogonality (`totient_mul_psiAP`, `sum_mainTerm`):
`φ(q) (ψ(x; q, a) − x/φ(q)) = Σ_χ χ(a)⁻¹ (ψ(x, χ) − E₀(χ) x)`. The triangle inequality over the
`φ(q)` characters gives `PsiAPBound C` from `PsiCharBound C` (`psiAPBound_of_psiCharBound`).

`0 ≤ ψ(x; q, a) − ϑ(x; q, a) ≤ ψ(x) − ϑ(x) ≤ 2 √x log x` (Mathlib's
`Chebyshev.psi_sub_theta_le`), and `2 √x log x ≤ 3 √x (log x)(log qx)` because
`log qx ≥ log 2`. So `ThetaAPBound (C + 3)` (`thetaAPBound_of_psiAPBound`).
-/

namespace PsiGRH

open DirichletCharacter ArithmeticFunction

variable {q : ℕ} [NeZero q]

/-- Orthogonality: `φ(q) ψ(x; q, a) = Σ_χ χ(a⁻¹) ψ(x, χ)` for `a` coprime to `q`. -/
lemma totient_mul_psiAP {a : ℕ} (ha : a.Coprime q) (x : ℝ) :
    (q.totient : ℂ) * (psiAP q a x : ℂ) =
      ∑ χ : DirichletCharacter ℂ q, χ ((a : ZMod q)⁻¹) * psiChar χ x := by
  classical
  have hu : IsUnit (a : ZMod q) := (ZMod.isUnit_iff_coprime a q).mpr ha
  unfold psiChar psiAP
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  have hterm : ∀ n : ℕ, ∑ χ : DirichletCharacter ℂ q, χ ((a : ZMod q)⁻¹) * ((Λ n : ℂ) * χ n) =
      (Λ n : ℂ) * (if (a : ZMod q) = n then (q.totient : ℂ) else 0) := by
    intro n
    rw [← sum_char_inv_mul_char_eq ℂ hu (n : ZMod q), Finset.mul_sum]
    exact Finset.sum_congr rfl fun χ _ => by ring
  simp_rw [hterm]
  push_cast
  rw [Finset.sum_filter, Finset.mul_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  have hiff : (a : ZMod q) = n ↔ n ≡ a [MOD q] := by
    rw [ZMod.natCast_eq_natCast_iff]; exact ⟨Nat.ModEq.symm, Nat.ModEq.symm⟩
  by_cases h : n ≡ a [MOD q]
  · rw [if_pos h, if_pos (hiff.mpr h)]; push_cast; ring
  · rw [if_neg h, if_neg (mt hiff.mp h)]; simp

/-- `Σ_χ χ(a⁻¹) E₀(χ) x = x`. -/
lemma sum_mainTerm {a : ℕ} (ha : a.Coprime q) (x : ℝ) :
    ∑ χ : DirichletCharacter ℂ q, χ ((a : ZMod q)⁻¹) * mainTerm χ x = x := by
  classical
  have hu : IsUnit (a : ZMod q) := (ZMod.isUnit_iff_coprime a q).mpr ha
  have hinv : IsUnit ((a : ZMod q)⁻¹) :=
    IsUnit.of_mul_eq_one (a : ZMod q) (ZMod.inv_mul_of_unit _ hu)
  simp only [mainTerm, mul_ite, mul_zero]
  rw [Finset.sum_ite_eq' Finset.univ (1 : DirichletCharacter ℂ q)]
  simp [MulChar.one_apply hinv]

/-- The number of characters mod `q` is `φ(q)`. -/
lemma card_characters : (Finset.univ : Finset (DirichletCharacter ℂ q)).card = q.totient := by
  rw [Finset.card_univ, ← Nat.card_eq_fintype_card]
  exact card_eq_totient_of_hasEnoughRootsOfUnity ℂ q

/-- `PsiCharBound C` implies `PsiAPBound C`. -/
theorem psiAPBound_of_psiCharBound {C : ℝ} (h : PsiCharBound C) : PsiAPBound C := by
  intro q a hq ha x hx
  haveI : NeZero q := ⟨by omega⟩
  have hφ : (0 : ℝ) < q.totient := by exact_mod_cast Nat.totient_pos.mpr hq
  have hφc : (q.totient : ℂ) ≠ 0 := by exact_mod_cast hφ.ne'
  have hid : Complex.ofReal ((q.totient : ℝ) * (psiAP q a x - x / q.totient)) =
      ∑ χ : DirichletCharacter ℂ q, χ ((a : ZMod q)⁻¹) * (psiChar χ x - mainTerm χ x) := by
    simp_rw [mul_sub, Finset.sum_sub_distrib]
    rw [sum_mainTerm ha, ← totient_mul_psiAP ha]
    push_cast
    field_simp
  have hnorm : (q.totient : ℝ) * |psiAP q a x - x / q.totient| ≤
      q.totient * (C * Real.sqrt x * Real.log x * Real.log (q * x)) := by
    have h1 : ‖Complex.ofReal ((q.totient : ℝ) * (psiAP q a x - x / q.totient))‖ =
        (q.totient : ℝ) * |psiAP q a x - x / q.totient| := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_of_pos hφ]
    rw [← h1, hid]
    refine (norm_sum_le _ _).trans ?_
    calc ∑ χ : DirichletCharacter ℂ q, ‖χ ((a : ZMod q)⁻¹) * (psiChar χ x - mainTerm χ x)‖
        ≤ ∑ _χ : DirichletCharacter ℂ q, C * Real.sqrt x * Real.log x * Real.log (q * x) := by
          refine Finset.sum_le_sum fun χ _ => ?_
          rw [norm_mul]
          have h1 := DirichletCharacter.norm_le_one χ ((a : ZMod q)⁻¹)
          have h2 := h q χ x hx
          calc ‖χ ((a : ZMod q)⁻¹)‖ * ‖psiChar χ x - mainTerm χ x‖
              ≤ 1 * ‖psiChar χ x - mainTerm χ x‖ := by gcongr
            _ ≤ _ := by linarith
      _ = _ := by rw [Finset.sum_const, card_characters, nsmul_eq_mul]
  exact le_of_mul_le_mul_left hnorm hφ

/-- `0 ≤ ψ(x; q, a) − ϑ(x; q, a) ≤ 2 √x log x`. -/
lemma psiAP_sub_thetaAP (q a : ℕ) {x : ℝ} (hx : 1 ≤ x) :
    0 ≤ psiAP q a x - thetaAP q a x ∧ psiAP q a x - thetaAP q a x ≤ 2 * Real.sqrt x * Real.log x := by
  classical
  have hsplit : psiAP q a x - thetaAP q a x =
      ∑ n ∈ (Finset.Icc 1 ⌊x⌋₊).filter (fun n => n ≡ a [MOD q] ∧ ¬ n.Prime), Λ n := by
    unfold psiAP thetaAP
    rw [Finset.sum_filter, Finset.sum_filter, Finset.sum_filter, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun n _ => ?_
    by_cases hm : n ≡ a [MOD q]
    · by_cases hp : n.Prime
      · simp [hm, hp, vonMangoldt_apply_prime hp]
      · simp [hm, hp]
    · simp [hm]
  rw [hsplit]
  refine ⟨Finset.sum_nonneg fun _ _ => vonMangoldt_nonneg, ?_⟩
  have hsub : ∑ n ∈ (Finset.Icc 1 ⌊x⌋₊).filter (fun n => n ≡ a [MOD q] ∧ ¬ n.Prime), Λ n ≤
      ∑ n ∈ (Finset.Ioc 0 ⌊x⌋₊).filter (fun n => ¬ n.Prime), Λ n := by
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun _ _ _ => vonMangoldt_nonneg)
    intro n hn
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_Ioc] at hn ⊢
    exact ⟨⟨by omega, hn.1.2⟩, hn.2.2⟩
  refine hsub.trans ?_
  rw [← Chebyshev.psi_sub_theta_eq_sum_not_prime]
  exact Chebyshev.psi_sub_theta_le hx

/-- `PsiAPBound C` implies `ThetaAPBound (C + 3)`. -/
theorem thetaAPBound_of_psiAPBound {C : ℝ} (hC : 0 ≤ C) (h : PsiAPBound C) :
    ThetaAPBound (C + 3) := by
  intro q a hq ha x hx
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hl2 := Real.log_two_gt_d9
  have hℓ : Real.log 2 ≤ Real.log x := Real.log_le_log (by norm_num) hx
  have hL : Real.log x ≤ Real.log (q * x) := Real.log_le_log (by linarith) (by nlinarith)
  have hs : 0 ≤ Real.sqrt x := Real.sqrt_nonneg x
  have hℓ0 : 0 ≤ Real.log x := by linarith
  obtain ⟨h0, h1⟩ := psiAP_sub_thetaAP q a (by linarith : (1 : ℝ) ≤ x)
  have hP := h q a hq ha x hx
  have hE : 2 * Real.sqrt x * Real.log x ≤ 3 * Real.sqrt x * Real.log x * Real.log (q * x) := by
    have : 0 ≤ Real.sqrt x * Real.log x := by positivity
    nlinarith
  rw [abs_le] at hP ⊢
  constructor <;> nlinarith

end PsiGRH
