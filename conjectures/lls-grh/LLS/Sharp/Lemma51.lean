import LLS.Sharp.Defs
import LLS.Sharp.Lemma51Aux.Basic

/-!
# A form of LLS Lemma 5.1

Write `w(n) = 1/(n log n) − 1/(x log x)`. Then
`Re W(χ, x) + l1Sum1 x + P2sum x / log x = Σ_{n ≤ x} Λ(n)(1 + Re χ(n)) w(n)`, every term is
nonnegative, and the powers `p^k ≤ x` of one prime `p ≤ √x` contribute at least
`−log(1 − p^{−2}) − 10/(3x)` (`L51.per_prime`). Summing over all primes `p ≤ √x` and comparing
with the Euler product of `ζ(2) = π²/6` gives `re_Wsum_ge`.
-/

namespace LLS.Sharp

open Real
open ArithmeticFunction (vonMangoldt)
open scoped ArithmeticFunction.vonMangoldt
open LLS.Sharp.L51

/-- The prime-by-prime gain over `−Σ Λ(n)(1/(n log n) − 1/(x log x))`, for any set `S` of primes
`p ≤ √x`. -/
theorem re_Wsum_ge_finset {M : ℕ} (χ : DirichletCharacter ℂ M) (x : ℕ) (hx : 4 ≤ x)
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime ∧ p ^ 2 ≤ x) :
    -(l1Sum1 x + P2sum x / Real.log x) + ∑ p ∈ S, -Real.log (1 - 1 / (p : ℝ) ^ 2)
        - 10 / 3 * (S.card : ℝ) / x
      ≤ (Wsum χ x).re := by
  have hx0 : (0 : ℝ) < x := by exact_mod_cast (show 0 < x by omega)
  have hl : 0 < Real.log x := Real.log_pos (by exact_mod_cast (show 1 < x by omega))
  set f : ℕ → ℝ := fun n =>
    (Λ n : ℝ) * (1 + (χ n).re) * (1 / ((n : ℝ) * Real.log n) - 1 / ((x : ℝ) * Real.log x))
    with hf
  have hsum : (Wsum χ x).re + (l1Sum1 x + P2sum x / Real.log x)
      = ∑ n ∈ Finset.range (x + 1), f n := by
    rw [re_Wsum_eq, l1Sum1_add_P2sum x (by omega), ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun n _ => ?_
    simp only [hf]; ring
  have hf0 : ∀ n ∈ Finset.range (x + 1), 0 ≤ f n := by
    intro n hn
    have hnx : n ≤ x := Nat.lt_succ_iff.1 (Finset.mem_range.1 hn)
    simp only [hf]
    by_cases h : (Λ n : ℝ) = 0
    · simp [h]
    have hn := two_le_of_vonMangoldt_ne_zero h
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    have hln : 0 < Real.log n := Real.log_pos (by exact_mod_cast (show 1 < n by omega))
    have hnxr : (n : ℝ) ≤ x := by exact_mod_cast hnx
    have hre := (re_pow_bounds (DirichletCharacter.norm_le_one χ (n : ZMod M)) 1).1
    rw [pow_one] at hre
    refine mul_nonneg (mul_nonneg ArithmeticFunction.vonMangoldt_nonneg hre) ?_
    rw [sub_nonneg]
    apply one_div_le_one_div_of_le (by positivity)
    exact mul_le_mul hnxr (Real.log_le_log hn0 hnxr) hln.le hx0.le
  -- the prime powers `p^(k+1)`, `p ∈ S`, `k < log_p x`
  set T := S.sigma fun p => Finset.range (Nat.log p x) with hT
  have hTsub : T.image (fun q => q.1 ^ (q.2 + 1)) ⊆ Finset.range (x + 1) := by
    intro n hn
    obtain ⟨⟨p, k⟩, hq, rfl⟩ := Finset.mem_image.1 hn
    rw [Finset.mem_sigma, Finset.mem_range] at hq
    have hp := (hS p hq.1).1
    have hx0' : x ≠ 0 := by omega
    rw [Finset.mem_range, Nat.lt_succ_iff]
    exact (Nat.pow_le_pow_right hp.pos hq.2).trans (Nat.pow_log_le_self p hx0')
  have hinj : Set.InjOn (fun q : (_ : ℕ) × ℕ => q.1 ^ (q.2 + 1)) T := by
    intro ⟨p, k⟩ hq ⟨p', k'⟩ hq' h
    have hp := (hS p (Finset.mem_sigma.1 hq).1).1
    have hp' := (hS p' (Finset.mem_sigma.1 hq').1).1
    obtain ⟨rfl, rfl⟩ := Nat.Prime.pow_inj hp hp' h
    rfl
  have hdrop : ∑ p ∈ S, ∑ k ∈ Finset.range (Nat.log p x), f (p ^ (k + 1))
      ≤ ∑ n ∈ Finset.range (x + 1), f n := by
    rw [← Finset.sum_sigma (f := fun q : (_ : ℕ) × ℕ => f (q.1 ^ (q.2 + 1))), ← hT,
      ← Finset.sum_image hinj]
    exact Finset.sum_le_sum_of_subset_of_nonneg hTsub fun n hn _ => hf0 n hn
  have hpp : ∀ p ∈ S, -Real.log (1 - 1 / (p : ℝ) ^ 2) - 10 / 3 / x
      ≤ ∑ k ∈ Finset.range (Nat.log p x), f (p ^ (k + 1)) := by
    intro p hpS
    obtain ⟨hp, hpx⟩ := hS p hpS
    refine (per_prime hp hpx (DirichletCharacter.norm_le_one χ (p : ZMod M))).trans_eq ?_
    refine Finset.sum_congr rfl fun k _ => ?_
    have hlp : 0 < Real.log p := Real.log_pos (by exact_mod_cast hp.one_lt)
    have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
    simp only [hf]
    rw [ArithmeticFunction.vonMangoldt_apply_pow (Nat.succ_ne_zero k),
      ArithmeticFunction.vonMangoldt_apply_prime hp]
    push_cast
    rw [map_pow, Real.log_pow]
    push_cast
    field_simp
  have hsumS := Finset.sum_le_sum hpp
  rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul] at hsumS
  have e : (S.card : ℝ) * (10 / 3 / x) = 10 / 3 * (S.card : ℝ) / x := by ring
  rw [e] at hsumS
  linarith

/-- All primes `p ≤ √x`: the gain is `log ζ(2)` up to `O(1/√x)`. -/
theorem re_Wsum_ge {M : ℕ} (χ : DirichletCharacter ℂ M) (x : ℕ) (hx : 4 ≤ x) :
    -(l1Sum1 x + P2sum x / Real.log x) + Real.log (π ^ 2 / 6)
        - 10 / 3 / √(x : ℝ) - 4 / 3 / (√(x : ℝ) - 1)
      ≤ (Wsum χ x).re := by
  set N := Nat.sqrt x with hNdef
  set S := (Finset.range (N + 1)).filter Nat.Prime with hSdef
  have hS : ∀ p ∈ S, p.Prime ∧ p ^ 2 ≤ x := by
    intro p hp
    rw [hSdef, Finset.mem_filter, Finset.mem_range, Nat.lt_succ_iff] at hp
    exact ⟨hp.2, (Nat.pow_le_pow_left hp.1 2).trans (Nat.sqrt_le' x)⟩
  have hmain := re_Wsum_ge_finset χ x hx S hS
  have hx0 : (0 : ℝ) < x := by exact_mod_cast (show 0 < x by omega)
  have hN2 : 2 ≤ N := Nat.le_sqrt.2 (by omega)
  have hsx2 : (2 : ℝ) ≤ √(x : ℝ) := by
    rw [show (2 : ℝ) = √4 by rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt (by exact_mod_cast hx)
  have hsxx : √(x : ℝ) * √(x : ℝ) = x := Real.mul_self_sqrt hx0.le
  -- the cardinality term
  have hcard : (S.card : ℝ) ≤ √(x : ℝ) := by
    have hsub : S ⊆ Finset.Icc 1 N := by
      intro p hp
      rw [hSdef, Finset.mem_filter, Finset.mem_range, Nat.lt_succ_iff] at hp
      exact Finset.mem_Icc.2 ⟨hp.2.one_lt.le, hp.1⟩
    have := Finset.card_le_card hsub
    rw [Nat.card_Icc, Nat.add_sub_cancel] at this
    exact (Nat.cast_le.2 this).trans Real.nat_sqrt_le_real_sqrt
  have hcardx : 10 / 3 * (S.card : ℝ) / x ≤ 10 / 3 / √(x : ℝ) := by
    calc 10 / 3 * (S.card : ℝ) / x ≤ 10 / 3 * √(x : ℝ) / x := by gcongr
      _ = 10 / 3 * √(x : ℝ) / (√(x : ℝ) * √(x : ℝ)) := by rw [hsxx]
      _ = 10 / 3 / √(x : ℝ) := by field_simp
  -- the Euler-product term
  have hzeta : Real.log (π ^ 2 / 6) = ∑' n, Robin.bZ 2 n := by
    rw [← Robin.log_riemannZeta_re_eq_tsum one_lt_two]
    congr 1
    have : riemannZeta ((2 : ℝ) : ℂ) = ((π ^ 2 / 6 : ℝ) : ℂ) := by
      push_cast; exact riemannZeta_two
    rw [this, Complex.ofReal_re]
  have hsplit := summable_bZ_two.sum_add_tsum_nat_add (N + 1)
  have hfin : ∑ i ∈ Finset.range (N + 1), Robin.bZ 2 i
      = ∑ p ∈ S, -Real.log (1 - 1 / (p : ℝ) ^ 2) := by
    rw [hSdef, Finset.sum_filter]
    exact Finset.sum_congr rfl fun n _ => bZ_two n
  have htail := tail_bZ_two_le (N := N) (by omega)
  have hNr : √(x : ℝ) - 1 ≤ N := by
    have := Real.real_sqrt_lt_nat_sqrt_succ (a := x)
    rw [← hNdef] at this
    linarith
  have htail' : 4 / 3 / (N : ℝ) ≤ 4 / 3 / (√(x : ℝ) - 1) := by
    apply div_le_div_of_nonneg_left (by norm_num) (by linarith) hNr
  rw [hfin] at hsplit
  linarith

end LLS.Sharp
