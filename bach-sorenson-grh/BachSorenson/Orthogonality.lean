import BachSorenson.Character
import Erdos985.Analytic.Principal

/-!
# Step 3: the weighted sum over a residue class, from orthogonality

For a unit `a` mod `q`, write `T(a, x) = Σ_{n<x, n ≡ a} Λ(n) (1 - n/x)`. Orthogonality of
Dirichlet characters gives `φ(q) T(a, x) = Σ_χ χ(a⁻¹) bachSum χ x`. The principal character
contributes at least `x/2 − √x/20 − 3 − ω(q) log x` (`bach_principal_of_GRH`, minus the `n` not
coprime to `q`), each of the other `φ(q) − 1` characters at most `charBound q x` in norm. So

`φ(q) T(a, x) ≥ x/2 − √x/20 − 3 − ω(q) log x − (φ(q) − 1) B(q, x)`.
-/

namespace BachSorenson

open Complex ArithmeticFunction Finset Erdos985 Ankeny
open scoped Classical

/-- `T(a, x) = Σ_{n<x, n ≡ a (mod q)} Λ(n) (1 - n/x)`. -/
noncomputable def classSum (q : ℕ) (a : ZMod q) (x : ℕ) : ℝ :=
  ∑ n ∈ (range x).filter (fun n : ℕ => (n : ZMod q) = a), (Λ n : ℝ) * (1 - (n : ℝ) / x)

lemma classSum_orthogonality {q : ℕ} [NeZero q] {a : ZMod q} (ha : IsUnit a) (x : ℕ) :
    ((q.totient : ℂ)) * (classSum q a x : ℂ)
      = ∑ χ : DirichletCharacter ℂ q, χ a⁻¹ * bachSum χ x := by
  simp only [bachSum, mul_sum]
  rw [sum_comm]
  simp only [classSum, sum_filter]
  push_cast
  rw [mul_sum]
  refine sum_congr rfl fun n _ => ?_
  have h := DirichletCharacter.sum_char_inv_mul_char_eq ℂ ha (n : ZMod q)
  have e : ∑ χ : DirichletCharacter ℂ q, χ a⁻¹ * ((Λ n : ℂ) * χ n * (1 - (n : ℂ) / x))
      = (∑ χ : DirichletCharacter ℂ q, χ a⁻¹ * χ n) * ((Λ n : ℂ) * (1 - (n : ℂ) / x)) := by
    rw [sum_mul]; refine sum_congr rfl fun χ _ => by ring
  rw [e, h]
  by_cases han : (n : ZMod q) = a
  · simp [han]
  · have : a ≠ (n : ZMod q) := fun h => han h.symm
    simp [han, this]

lemma card_dirichletCharacter (q : ℕ) [NeZero q] :
    (Finset.univ : Finset (DirichletCharacter ℂ q)).card = q.totient := by
  rw [Finset.card_univ, ← Nat.card_eq_fintype_card,
    DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity]

/-- The principal character: `Re bachSum 1 x ≥ x/2 − √x/20 − 3 − ω(q) log x`. -/
lemma re_bachSum_one_ge (hGRH : DirichletLNonvanishingRightOfHalf) {q : ℕ} [NeZero q]
    (x : ℕ) (hx : 1 ≤ x) :
    (x : ℝ) / 2 - √(x : ℝ) / 20 - 3 - q.primeFactors.card * Real.log x
      ≤ (bachSum (1 : DirichletCharacter ℂ q) x).re := by
  have hq0 : q ≠ 0 := NeZero.ne q
  set S₀ : ℝ := ∑ n ∈ range x, (Λ n : ℝ) * (1 - (n : ℝ) / x) with hS₀
  set E₁ : ℝ := ∑ n ∈ (range x).filter (fun n => ¬ n.Coprime q), (Λ n : ℝ) with hE₁d
  have hre : S₀ - E₁ ≤ (bachSum (1 : DirichletCharacter ℂ q) x).re := by
    rw [re_bachSum, hS₀, hE₁d, sum_filter, ← sum_sub_distrib]
    refine sum_le_sum fun n hn => ?_
    obtain ⟨hw0, hw1⟩ := weight_mem (mem_range.1 hn)
    have hΛ : (0 : ℝ) ≤ Λ n := vonMangoldt_nonneg
    by_cases hc : n.Coprime q
    · have : ((1 : DirichletCharacter ℂ q) n) = 1 :=
        MulChar.one_apply ((ZMod.isUnit_iff_coprime n q).2 hc)
      simp [hc, this]
    · have : ((1 : DirichletCharacter ℂ q) n) = 0 :=
        MulChar.map_nonunit _ (fun h => hc ((ZMod.isUnit_iff_coprime n q).1 h))
      simp only [hc, this, not_false_eq_true, ite_true, Complex.zero_re, mul_zero]
      nlinarith
  have hE₁ : E₁ ≤ q.primeFactors.card * Real.log x := by
    refine (sum_vonMangoldt_le_sum_fiber x _ q.primeFactors ?_).trans ?_
    · intro n _ hc hpp
      obtain ⟨r, k, hr, hk, rfl⟩ := (isPrimePow_nat_iff n).1 hpp
      rw [Nat.Prime.pow_minFac hr hk.ne', Nat.mem_primeFactors]
      refine ⟨hr, ?_, hq0⟩
      by_contra hd
      exact hc (Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd hr).2 hd))
    · calc ∑ p ∈ q.primeFactors, ∑ n ∈ ppFiber x p, (Λ n : ℝ)
          ≤ ∑ p ∈ q.primeFactors, Real.log x := sum_le_sum fun p hp =>
            (sum_ppFiber_le x p (Nat.prime_of_mem_primeFactors hp)).trans
              (log_mul_natLog_le x p (Nat.prime_of_mem_primeFactors hp) hx)
        _ = q.primeFactors.card * Real.log x := by rw [sum_const, nsmul_eq_mul]
  have hprin := (abs_le.1 (Analytic.bach_principal_of_GRH hGRH x hx)).1
  linarith

/-- The class-sum lower bound under GRH. -/
theorem totient_mul_classSum_ge (hGRH : DirichletLNonvanishingRightOfHalf) {q : ℕ} [NeZero q]
    {a : ZMod q} (ha : IsUnit a) (x : ℕ) (hx : 144 ≤ x) :
    (x : ℝ) / 2 - √(x : ℝ) / 20 - 3 - q.primeFactors.card * Real.log x
        - ((q.totient : ℝ) - 1) * charBound q x
      ≤ q.totient * classSum q a x := by
  have hx1 : 1 ≤ x := by omega
  have horth := congrArg Complex.re (classSum_orthogonality ha x)
  rw [show ((q.totient : ℂ) * (classSum q a x : ℂ)) = ((q.totient * classSum q a x : ℝ) : ℂ) by
    push_cast; ring, Complex.ofReal_re] at horth
  rw [horth, Complex.re_sum, ← Finset.add_sum_erase _ _ (Finset.mem_univ 1)]
  have hu : IsUnit a⁻¹ := by
    obtain ⟨u, rfl⟩ := ha
    rw [ZMod.inv_coe_unit]; exact Units.isUnit _
  have h1 : ((1 : DirichletCharacter ℂ q) a⁻¹) = 1 := MulChar.one_apply hu
  rw [h1, one_mul]
  have hprin := re_bachSum_one_ge hGRH (q := q) x hx1
  have hrest : -(((univ : Finset (DirichletCharacter ℂ q)).erase 1).card * charBound q x)
      ≤ ∑ χ ∈ (univ : Finset (DirichletCharacter ℂ q)).erase 1, (χ a⁻¹ * bachSum χ x).re := by
    rw [← nsmul_eq_mul, ← sum_const, ← sum_neg_distrib]
    refine sum_le_sum fun χ hχ => ?_
    have hχ1 : χ ≠ 1 := (mem_erase.1 hχ).1
    have hn := norm_bachSum_le_charBound hGRH χ hχ1 x hx
    have hc : ‖χ a⁻¹‖ ≤ 1 := DirichletCharacter.norm_le_one χ _
    have hre := Complex.abs_re_le_norm (χ a⁻¹ * bachSum χ x)
    rw [norm_mul] at hre
    have : ‖χ a⁻¹‖ * ‖bachSum χ x‖ ≤ charBound q x :=
      (mul_le_of_le_one_left (norm_nonneg _) hc).trans hn
    rw [abs_le] at hre
    linarith [hre.1]
  have hcard : (((univ : Finset (DirichletCharacter ℂ q)).erase 1).card : ℝ) = q.totient - 1 := by
    rw [card_erase_of_mem (mem_univ _), card_dirichletCharacter]
    have : 1 ≤ q.totient := Nat.totient_pos.2 (Nat.pos_of_ne_zero (NeZero.ne q))
    push_cast [this]
    ring
  rw [hcard] at hrest
  linarith

end BachSorenson
