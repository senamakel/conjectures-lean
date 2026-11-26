import Erdos985.Indicator
import PrimitiveRootSq.Character

/-!
# The character-sum inequality behind the analytic step

Write `x = p`, `w(n) = 1 - n/p`, `S₀ = Σ_{n<p} Λ(n) w(n)`, `P` for the prime factors of `p - 1`
and `θ = ∏_{ℓ ∈ P} (1 - 1/ℓ)`. Suppose that every prime `q < p` that is a primitive root
modulo `p` has `q ^ (p - 1) ≡ 1 (mod p²)`. Then

`θ · (S₀ - (2^|P| - 1) B₁) ≤ (S₀ + (p - 1) B₂) / p`,

where `B₁` bounds `‖bachSum χ p‖` for the non-trivial characters modulo `p` and `B₂` bounds it
for the primitive non-trivial characters modulo `p²`.

Proof. Fix `ψ` of order `p - 1` modulo `p`, and `η` modulo `p²` as in `exists_eta`.

* `F(n) = ∏_{ℓ ∈ P} ((1 - 1/ℓ) - (1/ℓ) Σ_{0<i<ℓ} ψ(n)^{i(p-1)/ℓ})` is `1` if
  `ψ(n)^{(p-1)/ℓ} ≠ 1` for every `ℓ` (then `n` is a primitive root modulo `p`) and `0`
  otherwise. Expanding the product over subsets of `P` exactly as erdos-985 does
  (`Erdos985.principal_le_of_no_prime_primitive_root`) gives
  `Re Σ Λ w F ≥ θ S₀ - (2^|P| - 1) θ B₁`.
* `J(n) = Σ_{0 ≤ j < p} η(n)^j` is `p` if `η(n) = 1` and `0` otherwise. If `F(n) = 1` and
  `n = q^k`, then `q` is a primitive root modulo `p`, so `q^(p-1) ≡ 1 (mod p²)` by hypothesis,
  so `η(n) = 1`. Hence `Re(Λ w F) ≤ Re(Λ w J)/p` termwise.
* `Σ Λ w J = S₀ + Σ_{0<j<p} bachSum (η^j)`, and each `η^j` is primitive modulo `p²`.
-/

namespace PrimitiveRootSq

open ArithmeticFunction Finset Erdos985 Erdos985.Indicator

/-- The value of one factor of `F`. -/
lemma factor_val (ℓ : ℕ) (hℓ : 2 ≤ ℓ) (ζ : ℂ) (hζ : ζ ^ ℓ = 1) :
    ((-(1 / (ℓ : ℝ)) : ℝ) : ℂ) * (∑ i ∈ Ico 1 ℓ, ζ ^ i) + ((1 - 1 / (ℓ : ℝ) : ℝ) : ℂ)
      = if ζ = 1 then 0 else 1 := by
  have hs : ∑ i ∈ Ico 1 ℓ, ζ ^ i = (∑ i ∈ range ℓ, ζ ^ i) - 1 := by
    rw [range_eq_Ico, sum_eq_sum_Ico_succ_bot (by omega : 0 < ℓ), pow_zero]; ring
  have hℓ0 : (ℓ : ℂ) ≠ 0 := by exact_mod_cast (by omega : ℓ ≠ 0)
  rw [hs]
  split_ifs with h1
  · subst h1
    simp only [one_pow, sum_const, card_range, nsmul_eq_mul, mul_one]
    push_cast
    field_simp
    ring
  · rw [geom_sum_eq h1, hζ, sub_self, zero_div]
    push_cast
    field_simp
    ring

theorem key_inequality (p : ℕ) [hpf : Fact p.Prime] (hp2 : p ≠ 2) (B₁ B₂ : ℝ)
    (hB₁ : ∀ χ : DirichletCharacter ℂ p, χ ≠ 1 → ‖bachSum χ p‖ ≤ B₁)
    (hB₂ : ∀ χ : DirichletCharacter ℂ (p ^ 2), χ.IsPrimitive → χ ≠ 1 → ‖bachSum χ p‖ ≤ B₂)
    (hno : ∀ q, q.Prime → q < p → orderOf (q : ZMod p) = p - 1 →
      (q : ZMod (p ^ 2)) ^ (p - 1) = 1) :
    (∏ ℓ ∈ (p - 1).primeFactors, (1 - 1 / (ℓ : ℝ))) *
        (∑ n ∈ range p, (Λ n : ℝ) * (1 - (n : ℝ) / p)
          - ((2 : ℝ) ^ (p - 1).primeFactors.card - 1) * B₁)
      ≤ (∑ n ∈ range p, (Λ n : ℝ) * (1 - (n : ℝ) / p) + (p - 1) * B₂) / p := by
  classical
  have hp := hpf.out
  have hN : p - 1 ≠ 0 := by have := hp.two_le; omega
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp.pos
  obtain ⟨ψ, hψ⟩ : ∃ ψ : MulChar (ZMod p) ℂ, orderOf ψ = p - 1 :=
    MulChar.exists_mulChar_orderOf (ZMod p) (by rw [ZMod.card])
      (Complex.isPrimitiveRoot_exp (p - 1) hN)
  obtain ⟨η, hηp, hη1⟩ := exists_eta (p := p)
  set x : ℕ := p with hx
  set P := (p - 1).primeFactors with hP
  have hP2 : ∀ ℓ ∈ P, 2 ≤ ℓ := fun ℓ hℓ => (Nat.mem_primeFactors.mp hℓ).1.two_le
  set a : ℕ → ℝ := fun ℓ => 1 - 1 / (ℓ : ℝ) with ha
  set b : ℕ → ℝ := fun ℓ => -(1 / (ℓ : ℝ)) with hb
  set A : ℕ → ℕ → ℂ := fun ℓ n => ∑ i ∈ Ico 1 ℓ, ψ n ^ (i * ((p - 1) / ℓ)) with hA
  set F : ℕ → ℂ := fun n => ∏ ℓ ∈ P, ((b ℓ : ℂ) * A ℓ n + (a ℓ : ℂ)) with hF
  set J : ℕ → ℂ := fun n => ∑ j ∈ range p, η n ^ j with hJ
  set c : ℕ → ℝ := fun n => (Λ n : ℝ) * (1 - (n : ℝ) / x) with hc
  set S₀ : ℝ := ∑ n ∈ range x, c n with hS₀
  have hc0 : ∀ n ∈ range x, 0 ≤ c n := by
    intro n hn
    have : (n : ℝ) / x ≤ 1 := by
      rw [div_le_one (by exact_mod_cast hp.pos)]; exact_mod_cast (mem_range.mp hn).le
    exact mul_nonneg vonMangoldt_nonneg (by linarith)
  -- Step 1: expansion of `F` over subsets of `P`.
  have hsum : ∑ t ∈ P.powerset,
      (((∏ ℓ ∈ t, b ℓ) * ∏ ℓ ∈ P \ t, a ℓ : ℝ) : ℂ) * W p ψ x t
        = ∑ n ∈ range x, (Λ n : ℂ) * (1 - (n : ℂ) / x) * F n := by
    simp only [hF]
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
  have hW0 : W p ψ x ∅ = (S₀ : ℂ) := by simp [W, hS₀, hc]
  rw [hW0] at hsum
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
  set R : ℂ := ∑ t ∈ P.powerset.erase ∅,
      (((∏ ℓ ∈ t, b ℓ) * ∏ ℓ ∈ P \ t, a ℓ : ℝ) : ℂ) * W p ψ x t with hR
  have hRle : ‖R‖ ≤ ((2 : ℝ) ^ P.card - 1) * (θ * B₁) := by
    have hcard : ((P.powerset.erase ∅).card : ℝ) = (2 : ℝ) ^ P.card - 1 := by
      rw [Finset.card_erase_of_mem (Finset.empty_mem_powerset P), Finset.card_powerset,
        Nat.cast_sub Nat.one_le_two_pow]
      push_cast
      ring
    rw [← hcard]
    refine (norm_sum_le _ _).trans ?_
    rw [← nsmul_eq_mul, ← Finset.sum_const]
    refine Finset.sum_le_sum fun t ht => ?_
    have htP : t ⊆ P := Finset.mem_powerset.mp (Finset.mem_of_mem_erase ht)
    have htne : t.Nonempty := Finset.nonempty_iff_ne_empty.mpr (Finset.ne_of_mem_erase ht)
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, ← hcoef t ht, mul_assoc]
    exact mul_le_mul_of_nonneg_left (norm_W_le p ψ hψ x B₁ hB₁ t htP htne) (abs_nonneg _)
  -- Step 2: termwise comparison of `F` with `J / p`.
  have hpoint : ∀ n ∈ range x, ((c n : ℂ) * F n).re ≤ ((c n : ℂ) * J n).re / p := by
    intro n hn
    have hnp : n < p := mem_range.mp hn
    by_cases hΛ : Λ n = 0
    · simp [hc, hΛ]
    obtain ⟨q, k, hq, hk, hqk⟩ := (isPrimePow_nat_iff _).mp (vonMangoldt_ne_zero_iff.mp hΛ)
    have hqn : q ≤ n := hqk ▸ Nat.le_self_pow hk.ne' q
    have hn0 : 0 < n := hqk ▸ pow_pos hq.pos k
    have hpn : ¬ p ∣ n := fun h => absurd (Nat.le_of_dvd hn0 h) (by omega)
    have hnZ : (n : ZMod p) ≠ 0 := by rwa [Ne, ZMod.natCast_eq_zero_iff]
    have hnU : IsUnit (n : ZMod p) := hnZ.isUnit
    have hnU2 : IsUnit (n : ZMod (p ^ 2)) := by
      rw [ZMod.isUnit_iff_coprime]
      exact Nat.Coprime.pow_right 2 ((Nat.coprime_comm).mp ((Nat.Prime.coprime_iff_not_dvd hp).mpr hpn))
    -- the values of `J`
    have hJval : (η n = 1 → J n = p) ∧ (η n ≠ 1 → J n = 0) := by
      refine ⟨fun h => ?_, fun h => ?_⟩
      · simp [hJ, h]
      · simp only [hJ]
        rw [geom_sum_eq h, hηp _ hnU2, sub_self, zero_div]
    -- the values of `F`
    have hζ : ∀ ℓ ∈ P, (ψ n ^ ((p - 1) / ℓ)) ^ ℓ = 1 := by
      intro ℓ hℓ
      have hd : ℓ ∣ p - 1 := (Nat.mem_primeFactors.mp hℓ).2.1
      rw [← pow_mul, Nat.div_mul_cancel hd, ← MulChar.pow_apply' _ hN, ← hψ,
        pow_orderOf_eq_one, MulChar.one_apply hnU]
    have hfac : ∀ ℓ ∈ P, (b ℓ : ℂ) * A ℓ n + (a ℓ : ℂ)
        = if ψ n ^ ((p - 1) / ℓ) = 1 then 0 else 1 := by
      intro ℓ hℓ
      rw [← factor_val ℓ (hP2 ℓ hℓ) _ (hζ ℓ hℓ)]
      simp only [hA, ha, hb]
      congr 2
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [pow_mul']
    have hcR : (0 : ℝ) ≤ c n := hc0 n hn
    by_cases hall : ∀ ℓ ∈ P, ψ n ^ ((p - 1) / ℓ) ≠ 1
    · -- `F n = 1`, and `n` is a primitive root modulo `p`
      have hF1 : F n = 1 := by
        simp only [hF]
        rw [Finset.prod_congr rfl hfac]
        exact Finset.prod_eq_one fun ℓ hℓ => by rw [if_neg (hall ℓ hℓ)]
      have hord : orderOf (n : ZMod p) = p - 1 := by
        apply orderOf_eq_of_pow_and_pow_div_prime (by omega)
        · exact ZMod.pow_card_sub_one_eq_one hnZ
        · intro ℓ hℓ hℓd h1
          apply hall ℓ (Nat.mem_primeFactors.mpr ⟨hℓ, hℓd, hN⟩)
          rw [← map_pow, h1, map_one]
      have hqZ : (q : ZMod p) ≠ 0 := by
        rw [Ne, ZMod.natCast_eq_zero_iff]
        intro h; have := Nat.le_of_dvd hq.pos h; omega
      have hordq : orderOf (q : ZMod p) = p - 1 := by
        rw [← hqk, Nat.cast_pow] at hord
        exact Nat.dvd_antisymm (ZMod.orderOf_dvd_card_sub_one hqZ) (hord ▸ orderOf_pow_dvd k)
      have hW : (n : ZMod (p ^ 2)) ^ (p - 1) = 1 := by
        rw [← hqk, Nat.cast_pow, ← pow_mul, mul_comm, pow_mul, hno q hq (by omega) hordq, one_pow]
      have hη : η n = 1 := by
        have h1 : η n ^ (p - 1) = 1 := by rw [← map_pow, hW, map_one]
        have h2 := hηp _ hnU2
        rw [show p = (p - 1) + 1 by omega, pow_succ, h1, one_mul] at h2
        exact h2
      rw [hF1, hJval.1 hη, mul_one]
      rw [show ((c n : ℂ) * (p : ℂ)) = ((c n * p : ℝ) : ℂ) by push_cast; ring, Complex.ofReal_re,
        Complex.ofReal_re, mul_div_assoc, div_self hpR.ne', mul_one]
    · -- `F n = 0`
      push_neg at hall
      obtain ⟨ℓ, hℓ, h1⟩ := hall
      have hF0 : F n = 0 := by
        simp only [hF]
        exact Finset.prod_eq_zero hℓ (by rw [hfac ℓ hℓ, if_pos h1])
      rw [hF0, mul_zero, Complex.zero_re]
      by_cases hη : η n = 1
      · rw [hJval.1 hη, show ((c n : ℂ) * (p : ℂ)) = ((c n * p : ℝ) : ℂ) by push_cast; ring,
          Complex.ofReal_re]
        positivity
      · rw [hJval.2 hη, mul_zero, Complex.zero_re, zero_div]
  -- Step 3: `Σ c J = S₀ + Σ_{0<j<p} bachSum (η^j)`.
  have hJsum : ∑ n ∈ range x, (c n : ℂ) * J n
      = (S₀ : ℂ) + ∑ j ∈ Ico 1 p, bachSum (η ^ j) x := by
    simp only [hJ, Finset.mul_sum]
    rw [Finset.sum_comm, range_eq_Ico, sum_eq_sum_Ico_succ_bot (by have := hp.pos; omega)]
    congr 1
    · simp [hS₀]
    · refine Finset.sum_congr rfl fun j hj => ?_
      have hj0 : j ≠ 0 := by have := (mem_Ico.mp hj).1; omega
      simp only [bachSum, hc]
      refine Finset.sum_congr rfl fun n _ => ?_
      rw [MulChar.pow_apply' _ hj0]
      push_cast
      ring
  have hJre : (∑ n ∈ range x, (c n : ℂ) * J n).re ≤ S₀ + (p - 1) * B₂ := by
    rw [hJsum, Complex.add_re, Complex.ofReal_re]
    have : (∑ j ∈ Ico 1 p, bachSum (η ^ j) x).re ≤ (p - 1) * B₂ := by
      refine (Complex.re_le_norm _).trans ((norm_sum_le _ _).trans ?_)
      have hcard : ((Ico 1 p).card : ℝ) = p - 1 := by
        rw [Nat.card_Ico, Nat.cast_sub hp.one_lt.le, Nat.cast_one]
      rw [← hcard, ← nsmul_eq_mul, ← Finset.sum_const]
      refine Finset.sum_le_sum fun j hj => ?_
      obtain ⟨hj1, hjp⟩ := mem_Ico.mp hj
      have hne : (η ^ j) (1 + (p : ZMod (p ^ 2))) ≠ 1 := by
        rw [MulChar.pow_apply' _ (by omega)]; exact hη1 j (by omega) hjp
      refine hB₂ _ (isPrimitive_of_apply_one_add_ne_one hne) ?_
      rintro h; rw [h, MulChar.one_apply (by
        rw [show (1 + (p : ZMod (p ^ 2))) = ((1 + p : ℕ) : ZMod (p ^ 2)) by push_cast; ring,
          ZMod.isUnit_iff_coprime]
        exact Nat.Coprime.pow_right 2 (by simp))] at hne
      exact hne rfl
    linarith
  -- Step 4: combine.
  have hFre : θ * S₀ - ((2 : ℝ) ^ P.card - 1) * (θ * B₁)
      ≤ (∑ n ∈ range x, (Λ n : ℂ) * (1 - (n : ℂ) / x) * F n).re := by
    rw [← hsum, Complex.add_re, ← Complex.ofReal_mul, Complex.ofReal_re]
    have := (Complex.abs_re_le_norm R).trans hRle
    have := neg_abs_le R.re
    linarith
  have hFc : ∑ n ∈ range x, (Λ n : ℂ) * (1 - (n : ℂ) / x) * F n
      = ∑ n ∈ range x, (c n : ℂ) * F n := by
    refine Finset.sum_congr rfl fun n _ => ?_
    simp only [hc]; push_cast; ring
  rw [hFc, Complex.re_sum] at hFre
  have hsumle : ∑ n ∈ range x, ((c n : ℂ) * F n).re
      ≤ (∑ n ∈ range x, (c n : ℂ) * J n).re / p := by
    rw [Complex.re_sum, Finset.sum_div]
    exact Finset.sum_le_sum hpoint
  have hfin : θ * S₀ - ((2 : ℝ) ^ P.card - 1) * (θ * B₁) ≤ (S₀ + (p - 1) * B₂) / p :=
    hFre.trans (hsumle.trans (div_le_div_of_nonneg_right hJre hpR.le))
  calc θ * (S₀ - ((2 : ℝ) ^ P.card - 1) * B₁)
      = θ * S₀ - ((2 : ℝ) ^ P.card - 1) * (θ * B₁) := by ring
    _ ≤ _ := hfin

end PrimitiveRootSq
