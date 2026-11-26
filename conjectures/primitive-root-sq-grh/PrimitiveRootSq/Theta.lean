import Mathlib

/-!
# A lower bound for `θ = φ(n)/n = ∏_{ℓ ∣ n} (1 - 1/ℓ)`

Split the prime factors of `n` at 29: the ones below 29 contribute at least the product over all
primes below 29, `36495360 / 223092870 ≈ 0.16359`, and each of the others at least `28/29`.
-/

namespace PrimitiveRootSq

open Finset

/-- `∏_{ℓ ∣ n} (1 - 1/ℓ) ≥ (36495360 / 223092870) · (28/29)^ω(n)`. -/
theorem theta_ge (n : ℕ) :
    (36495360 / 223092870 : ℝ) * (28 / 29) ^ n.primeFactors.card
      ≤ ∏ ℓ ∈ n.primeFactors, (1 - 1 / (ℓ : ℝ)) := by
  classical
  set P := n.primeFactors with hP
  set f : ℕ → ℝ := fun ℓ => 1 - 1 / (ℓ : ℝ) with hf
  have hprime : ∀ ℓ ∈ P, ℓ.Prime := fun ℓ hℓ => (Nat.mem_primeFactors.mp hℓ).1
  have hf0 : ∀ ℓ : ℕ, ℓ.Prime → 0 ≤ f ℓ := by
    intro ℓ hℓ
    have : (2 : ℝ) ≤ ℓ := by exact_mod_cast hℓ.two_le
    simp only [hf]; rw [sub_nonneg, div_le_one (by linarith)]; linarith
  have hf1 : ∀ ℓ : ℕ, f ℓ ≤ 1 := by
    intro ℓ; simp only [hf]
    have : 0 ≤ 1 / (ℓ : ℝ) := by positivity
    linarith
  set S := (range 29).filter Nat.Prime with hS
  set Ps := P.filter (· < 29) with hPs
  set Pl := P.filter (fun ℓ => ¬ ℓ < 29) with hPl
  have hsplit : ∏ ℓ ∈ P, f ℓ = (∏ ℓ ∈ Ps, f ℓ) * ∏ ℓ ∈ Pl, f ℓ :=
    (prod_filter_mul_prod_filter_not P (· < 29) f).symm
  -- the small primes
  have hsub : Ps ⊆ S := by
    intro ℓ hℓ
    simp only [hPs, mem_filter] at hℓ
    simp only [hS, mem_filter, mem_range]
    exact ⟨hℓ.2, hprime ℓ hℓ.1⟩
  have hSval : ∏ ℓ ∈ S, f ℓ = 36495360 / 223092870 := by
    rw [show S = {2, 3, 5, 7, 11, 13, 17, 19, 23} by decide]
    simp only [hf]
    norm_num [prod_insert]
  have hsmall : (36495360 / 223092870 : ℝ) ≤ ∏ ℓ ∈ Ps, f ℓ := by
    rw [← hSval, ← prod_sdiff hsub]
    have h1 : ∏ ℓ ∈ S \ Ps, f ℓ ≤ 1 := by
      refine prod_le_one₀ (fun ℓ hℓ => hf0 ℓ ?_) (fun ℓ _ => hf1 ℓ)
      have := (mem_sdiff.mp hℓ).1
      simp only [hS, mem_filter] at this
      exact this.2
    have h2 : 0 ≤ ∏ ℓ ∈ Ps, f ℓ :=
      prod_nonneg fun ℓ hℓ => hf0 ℓ (hprime ℓ (mem_filter.mp hℓ).1)
    nlinarith
  -- the large primes
  have hlarge : (28 / 29 : ℝ) ^ P.card ≤ ∏ ℓ ∈ Pl, f ℓ := by
    have hc : Pl.card ≤ P.card := card_filter_le _ _
    calc (28 / 29 : ℝ) ^ P.card ≤ (28 / 29) ^ Pl.card :=
          pow_le_pow_of_le_one (by norm_num) (by norm_num) hc
      _ = ∏ _ℓ ∈ Pl, (28 / 29 : ℝ) := (prod_const _).symm
      _ ≤ ∏ ℓ ∈ Pl, f ℓ := by
          refine prod_le_prod₀ (fun _ _ => by norm_num) fun ℓ hℓ => ?_
          simp only [hPl, mem_filter, not_lt] at hℓ
          have : (29 : ℝ) ≤ ℓ := by exact_mod_cast hℓ.2
          simp only [hf]
          rw [show (28 / 29 : ℝ) = 1 - 1 / 29 by norm_num]
          have : 1 / (ℓ : ℝ) ≤ 1 / 29 := one_div_le_one_div_of_le (by norm_num) this
          linarith
  rw [hsplit]
  exact mul_le_mul hsmall hlarge (by positivity)
    (prod_nonneg fun ℓ hℓ => hf0 ℓ (hprime ℓ (mem_filter.mp hℓ).1))

end PrimitiveRootSq
