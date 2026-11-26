import Erdos985.Bach
import Erdos985.Indicator.Lemmas

namespace Erdos985

/-!
# Character expansion of the primitive-root indicator  (MTT §2, proof of Theorem 2)

If no prime `q < x` (with `x ≤ p`) is a primitive root mod `p`, then the principal weighted
prime sum is at most `(2^ω(p-1) - 1)` times a uniform bound for the non-principal ones.

Proof sketch.  Fix a character `ψ` of order `N = p - 1`.  For a prime `ℓ ∣ N`, the characters
`ψ^{iN/ℓ}`, `1 ≤ i < ℓ`, are those of order `ℓ`.  For every `n < x` with `Λ n ≠ 0` the residue
of `n` is not a primitive root, so some `ψ(n)^{N/ℓ} = 1`, and hence
`∏_{ℓ ∣ N} ((1 - 1/ℓ) - (1/ℓ) Σ_{1 ≤ i < ℓ} ψ(n)^{iN/ℓ}) = 0`.  Expanding the product over
subsets `T` of the prime divisors, the `T = ∅` term is `θ · S₀` with `θ = ∏ (1 - 1/ℓ)`, and
each nonempty `T` contributes a sum of `∏_{ℓ∈T}(ℓ-1)` non-principal `bachSum`s with
coefficient of absolute value `∏_{ℓ∉T}(1-1/ℓ) ∏_{ℓ∈T} 1/ℓ`, i.e. at most `θ · B` in total.
-/

open ArithmeticFunction Finset Erdos985.Indicator

theorem principal_le_of_no_prime_primitive_root (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2)
    (x : ℕ) (hxp : x ≤ p) (B : ℝ)
    (hB : ∀ χ : DirichletCharacter ℂ p, χ ≠ 1 → ‖bachSum χ x‖ ≤ B)
    (hno : ∀ q, q.Prime → q < x → orderOf (q : ZMod p) ≠ p - 1) :
    ∑ n ∈ Finset.range x, (Λ n : ℝ) * (1 - (n : ℝ) / x)
      ≤ ((2 : ℝ) ^ (p - 1).primeFactors.card - 1) * B := by
  classical
  have hN : p - 1 ≠ 0 := by
    have := (Fact.out : p.Prime).two_le; omega
  obtain ⟨ψ, hψ⟩ : ∃ ψ : MulChar (ZMod p) ℂ, orderOf ψ = p - 1 :=
    MulChar.exists_mulChar_orderOf (ZMod p) (by rw [ZMod.card])
      (Complex.isPrimitiveRoot_exp (p - 1) hN)
  set P := (p - 1).primeFactors with hP
  have hP2 : ∀ ℓ ∈ P, 2 ≤ ℓ := fun ℓ hℓ => (Nat.mem_primeFactors.mp hℓ).1.two_le
  set a : ℕ → ℝ := fun ℓ => 1 - 1 / (ℓ : ℝ) with ha
  set b : ℕ → ℝ := fun ℓ => -(1 / (ℓ : ℝ)) with hb
  set A : ℕ → ℕ → ℂ := fun ℓ n => ∑ i ∈ Ico 1 ℓ, ψ n ^ (i * ((p - 1) / ℓ)) with hA
  set S₀ : ℝ := ∑ n ∈ Finset.range x, (Λ n : ℝ) * (1 - (n : ℝ) / x) with hS₀
  -- Step 1: the product vanishes on the support of `Λ`.
  have h0 : ∀ n ∈ range x,
      (Λ n : ℂ) * (1 - (n : ℂ) / x) * ∏ ℓ ∈ P, ((b ℓ : ℂ) * A ℓ n + (a ℓ : ℂ)) = 0 := by
    intro n hn
    by_cases hΛ : Λ n = 0
    · simp [hΛ]
    obtain ⟨hn0, hord⟩ := orderOf_ne_of_vonMangoldt_ne_zero p x hxp hno (mem_range.mp hn) hΛ
    obtain ⟨ℓ, hℓ, hpow⟩ := exists_primeFactor_pow_eq_one p hn0 hord
    rw [Finset.prod_eq_zero hℓ, mul_zero]
    have hψ1 : ψ n ^ ((p - 1) / ℓ) = 1 := by rw [← map_pow, hpow, map_one]
    have hℓ1 : 1 ≤ ℓ := (hP2 ℓ hℓ).trans' (by norm_num)
    have hAℓ : A ℓ n = (ℓ : ℂ) - 1 := by
      simp only [hA]
      simp_rw [pow_mul', hψ1, one_pow]
      rw [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul, mul_one, Nat.cast_sub hℓ1, Nat.cast_one]
    rw [hAℓ]
    have : (ℓ : ℂ) ≠ 0 := by exact_mod_cast (by omega : ℓ ≠ 0)
    simp only [ha, hb]
    push_cast
    field_simp
    ring
  -- Step 2: expand the product over subsets of `P`.
  have hsum : ∑ t ∈ P.powerset,
      (((∏ ℓ ∈ t, b ℓ) * ∏ ℓ ∈ P \ t, a ℓ : ℝ) : ℂ) * W p ψ x t = 0 := by
    rw [← Finset.sum_eq_zero h0]
    simp_rw [Finset.prod_add, Finset.mul_sum, W, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun t _ => Finset.sum_congr rfl fun n _ => ?_
    rw [Finset.prod_mul_distrib]
    push_cast
    ring
  rw [← Finset.add_sum_erase _ _ (Finset.empty_mem_powerset P)] at hsum
  simp only [Finset.prod_empty, one_mul, Finset.sdiff_empty] at hsum
  set θ : ℝ := ∏ ℓ ∈ P, a ℓ with hθ
  have ha_pos : ∀ ℓ ∈ P, 0 < a ℓ := by
    intro ℓ hℓ
    have h2 : (2 : ℝ) ≤ ℓ := by exact_mod_cast hP2 ℓ hℓ
    simp only [ha]
    rw [sub_pos, div_lt_one (by linarith)]
    linarith
  have hθpos : 0 < θ := Finset.prod_pos ha_pos
  have hW0 : W p ψ x ∅ = (S₀ : ℂ) := by
    simp [W, hS₀]
  rw [hW0] at hsum
  -- Step 3: bound the nonempty terms.
  have hcoef : ∀ t ∈ P.powerset.erase ∅,
      |(∏ ℓ ∈ t, b ℓ) * ∏ ℓ ∈ P \ t, a ℓ| * (∏ ℓ ∈ t, ((ℓ : ℝ) - 1)) = θ := by
    intro t ht
    have htP : t ⊆ P := Finset.mem_powerset.mp (Finset.mem_of_mem_erase ht)
    rw [abs_mul, Finset.abs_prod, abs_of_nonneg (Finset.prod_nonneg fun ℓ hℓ =>
      (ha_pos ℓ (Finset.sdiff_subset hℓ)).le), mul_comm, ← mul_assoc, ← Finset.prod_mul_distrib,
      hθ, ← Finset.prod_sdiff htP, mul_comm]
    congr 1
    refine Finset.prod_congr rfl fun ℓ hℓ => ?_
    have h2 : (2 : ℝ) ≤ ℓ := by exact_mod_cast hP2 ℓ (htP hℓ)
    simp only [ha, hb, abs_neg]
    rw [abs_of_pos (by positivity)]
    field_simp
  have hbound : ‖((θ : ℝ) : ℂ) * (S₀ : ℂ)‖ ≤ ((P.powerset.erase ∅).card : ℝ) * (θ * B) := by
    rw [eq_neg_of_add_eq_zero_left hsum, norm_neg]
    refine (norm_sum_le _ _).trans ?_
    rw [← nsmul_eq_mul, ← Finset.sum_const]
    refine Finset.sum_le_sum fun t ht => ?_
    have htP : t ⊆ P := Finset.mem_powerset.mp (Finset.mem_of_mem_erase ht)
    have htne : t.Nonempty := Finset.nonempty_iff_ne_empty.mpr (Finset.ne_of_mem_erase ht)
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, ← hcoef t ht, mul_assoc]
    exact mul_le_mul_of_nonneg_left (norm_W_le p ψ hψ x B hB t htP htne) (abs_nonneg _)
  have hcard : ((P.powerset.erase ∅).card : ℝ) = (2 : ℝ) ^ P.card - 1 := by
    rw [Finset.card_erase_of_mem (Finset.empty_mem_powerset P), Finset.card_powerset,
      Nat.cast_sub Nat.one_le_two_pow]
    push_cast
    ring
  rw [hcard] at hbound
  have hle : θ * S₀ ≤ θ * (((2 : ℝ) ^ P.card - 1) * B) := by
    calc θ * S₀ ≤ |θ * S₀| := le_abs_self _
      _ = ‖((θ : ℝ) : ℂ) * (S₀ : ℂ)‖ := by
          rw [← Complex.ofReal_mul, Complex.norm_real, Real.norm_eq_abs]
      _ ≤ _ := hbound
      _ = θ * (((2 : ℝ) ^ P.card - 1) * B) := by ring
  exact le_of_mul_le_mul_left hle hθpos

end Erdos985
