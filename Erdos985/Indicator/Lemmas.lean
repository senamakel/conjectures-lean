import Erdos985.Bach

/-!
# Auxiliary lemmas for the character expansion of the primitive-root indicator
-/

open ArithmeticFunction

namespace Erdos985.Indicator

/-- A nonzero residue that is not a primitive root satisfies `a ^ ((p-1)/ℓ) = 1` for some
prime `ℓ ∣ p - 1`. -/
lemma exists_primeFactor_pow_eq_one (p : ℕ) [Fact p.Prime] {a : ZMod p} (ha : a ≠ 0)
    (hord : orderOf a ≠ p - 1) : ∃ ℓ ∈ (p - 1).primeFactors, a ^ ((p - 1) / ℓ) = 1 := by
  have hd : orderOf a ∣ p - 1 := ZMod.orderOf_dvd_card_sub_one ha
  have hN : p - 1 ≠ 0 := by
    have := (Fact.out : p.Prime).two_le; omega
  have hq : (p - 1) / orderOf a ≠ 1 := by
    intro h
    exact hord (Nat.eq_of_dvd_of_div_eq_one hd h)
  obtain ⟨ℓ, hℓ, hℓd⟩ := Nat.exists_prime_and_dvd hq
  have hℓN : ℓ ∣ p - 1 := hℓd.trans (Nat.div_dvd_of_dvd hd)
  refine ⟨ℓ, Nat.mem_primeFactors.mpr ⟨hℓ, hℓN, hN⟩, ?_⟩
  rw [← orderOf_dvd_iff_pow_eq_one]
  apply Nat.dvd_div_of_mul_dvd
  rw [mul_comm]
  calc orderOf a * ℓ ∣ orderOf a * ((p - 1) / orderOf a) := Nat.mul_dvd_mul_left _ hℓd
    _ = p - 1 := Nat.mul_div_cancel' hd

/-- Under the no-small-prime-primitive-root hypothesis, prime powers below `x` are not
primitive roots. -/
lemma orderOf_ne_of_vonMangoldt_ne_zero (p : ℕ) [Fact p.Prime] (x : ℕ) (hxp : x ≤ p)
    (hno : ∀ q, q.Prime → q < x → orderOf (q : ZMod p) ≠ p - 1) {n : ℕ} (hn : n < x)
    (hΛ : Λ n ≠ 0) : (n : ZMod p) ≠ 0 ∧ orderOf (n : ZMod p) ≠ p - 1 := by
  obtain ⟨q, k, hq, hk, rfl⟩ := (isPrimePow_nat_iff _).mp (vonMangoldt_ne_zero_iff.mp hΛ)
  have hqn : q ≤ q ^ k := Nat.le_self_pow hk.ne' q
  have hqp : (q : ZMod p) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]
    intro h
    have := Nat.le_of_dvd hq.pos h
    omega
  have hn0 : ((q ^ k : ℕ) : ZMod p) ≠ 0 := by
    rw [Nat.cast_pow]; exact pow_ne_zero _ hqp
  refine ⟨hn0, fun h => hno q hq (by omega) ?_⟩
  rw [Nat.cast_pow] at h
  have h1 : orderOf ((q : ZMod p) ^ k) ∣ orderOf (q : ZMod p) := orderOf_pow_dvd k
  exact Nat.dvd_antisymm (ZMod.orderOf_dvd_card_sub_one hqp) (h ▸ h1)

/-- Arithmetic heart of the nontriviality: a sum `Σ_{ℓ ∈ T} c_ℓ N/ℓ` with `T` a nonempty set of
distinct prime divisors of `N` and `0 < c_ℓ < ℓ` is not divisible by `N`. -/
lemma not_dvd_sum (N : ℕ) (T : Finset ℕ) (hT : T ⊆ N.primeFactors) (c : T → ℕ)
    (hc : ∀ ℓ, 0 < c ℓ ∧ c ℓ < (ℓ : ℕ)) (ℓ₀ : T) :
    ¬ N ∣ ∑ ℓ : T, c ℓ * (N / ℓ) := by
  classical
  intro hdiv
  have hmem : ∀ ℓ : T, (ℓ : ℕ).Prime ∧ (ℓ : ℕ) ∣ N ∧ N ≠ 0 :=
    fun ℓ => Nat.mem_primeFactors.mp (hT ℓ.2)
  set M := ∏ ℓ ∈ Finset.univ.erase ℓ₀, (ℓ : ℕ) with hM
  have h1 : N ∣ M * ∑ ℓ : T, c ℓ * (N / ℓ) := dvd_mul_of_dvd_right hdiv M
  rw [Finset.mul_sum, ← Finset.add_sum_erase _ _ (Finset.mem_univ ℓ₀)] at h1
  have h2 : N ∣ ∑ ℓ ∈ Finset.univ.erase ℓ₀, M * (c ℓ * (N / ℓ)) := by
    apply Finset.dvd_sum
    intro ℓ hℓ
    obtain ⟨M', hM'⟩ := Finset.dvd_prod_of_mem (fun ℓ : T => (ℓ : ℕ)) hℓ
    rw [← hM] at hM'
    rw [hM']
    have : (ℓ : ℕ) * (N / ℓ) = N := Nat.mul_div_cancel' (hmem ℓ).2.1
    exact ⟨M' * c ℓ, by
      rw [show (ℓ : ℕ) * M' * (c ℓ * (N / ℓ)) = ((ℓ : ℕ) * (N / ℓ)) * (M' * c ℓ) by ring, this]⟩
  have h3 : N ∣ M * (c ℓ₀ * (N / ℓ₀)) := (Nat.dvd_add_left h2).mp h1
  obtain ⟨hp0, hd0, hN0⟩ := hmem ℓ₀
  have hpos : 0 < N / ℓ₀ := Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hN0) hd0) hp0.pos
  have h4 : (ℓ₀ : ℕ) ∣ M * c ℓ₀ := by
    have : (ℓ₀ : ℕ) * (N / ℓ₀) ∣ (M * c ℓ₀) * (N / ℓ₀) := by
      rw [Nat.mul_div_cancel' hd0, mul_assoc]; exact h3
    exact Nat.dvd_of_mul_dvd_mul_right hpos this
  rcases (Nat.Prime.dvd_mul hp0).mp h4 with h | h
  · rw [hM] at h
    obtain ⟨ℓ, hℓ, hdl⟩ := (hp0.prime.dvd_finsetProd_iff _).mp h
    have := (Nat.prime_dvd_prime_iff_eq hp0 (hmem ℓ).1).mp hdl
    exact (Finset.mem_erase.mp hℓ).1 (Subtype.ext this).symm
  · have := Nat.le_of_dvd (hc ℓ₀).1 h
    have := (hc ℓ₀).2
    omega

end Erdos985.Indicator

namespace Erdos985.Indicator

open Finset

/-- The weighted sum attached to a set `T` of prime divisors of `p - 1`. -/
noncomputable def W (p : ℕ) (ψ : DirichletCharacter ℂ p) (x : ℕ) (T : Finset ℕ) : ℂ :=
  ∑ n ∈ range x, (Λ n : ℂ) * (1 - (n : ℂ) / x) *
    ∏ ℓ ∈ T, ∑ i ∈ Ico 1 ℓ, ψ n ^ (i * ((p - 1) / ℓ))

lemma norm_W_le (p : ℕ) [Fact p.Prime] (ψ : DirichletCharacter ℂ p) (hψ : orderOf ψ = p - 1)
    (x : ℕ) (B : ℝ) (hB : ∀ χ : DirichletCharacter ℂ p, χ ≠ 1 → ‖bachSum χ x‖ ≤ B)
    (T : Finset ℕ) (hT : T ⊆ (p - 1).primeFactors) (hne : T.Nonempty) :
    ‖W p ψ x T‖ ≤ (∏ ℓ ∈ T, ((ℓ : ℝ) - 1)) * B := by
  classical
  obtain ⟨l, hl⟩ := hne
  set m : (T → ℕ) → ℕ := fun c => ∑ ℓ : T, c ℓ * ((p - 1) / ℓ) with hm
  have hndvd : ∀ c ∈ Fintype.piFinset (fun ℓ : T => Ico 1 (ℓ : ℕ)), ¬ (p - 1) ∣ m c := by
    intro c hc
    rw [Fintype.mem_piFinset] at hc
    refine not_dvd_sum (p - 1) T hT c (fun ℓ => ?_) ⟨l, hl⟩
    have := Finset.mem_Ico.mp (hc ℓ); omega
  have key : ∀ n : ℕ, ∏ ℓ ∈ T, ∑ i ∈ Ico 1 ℓ, ψ n ^ (i * ((p - 1) / ℓ)) =
      ∑ c ∈ Fintype.piFinset (fun ℓ : T => Ico 1 (ℓ : ℕ)), ψ n ^ m c := by
    intro n
    rw [← Finset.prod_coe_sort, Finset.prod_univ_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [Finset.prod_pow_eq_pow_sum]
  have hW : W p ψ x T = ∑ c ∈ Fintype.piFinset (fun ℓ : T => Ico 1 (ℓ : ℕ)),
      bachSum (ψ ^ m c) x := by
    unfold W bachSum
    simp_rw [key, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun c hc => Finset.sum_congr rfl fun n _ => ?_
    have hm0 : m c ≠ 0 := fun h => hndvd c hc (h ▸ dvd_zero (p - 1))
    rw [MulChar.pow_apply' _ hm0]
    ring
  rw [hW]
  calc ‖∑ c ∈ Fintype.piFinset (fun ℓ : T => Ico 1 (ℓ : ℕ)), bachSum (ψ ^ m c) x‖
      ≤ ∑ c ∈ Fintype.piFinset (fun ℓ : T => Ico 1 (ℓ : ℕ)), ‖bachSum (ψ ^ m c) x‖ :=
        norm_sum_le _ _
    _ ≤ ∑ _c ∈ Fintype.piFinset (fun ℓ : T => Ico 1 (ℓ : ℕ)), B := by
        refine Finset.sum_le_sum fun c hc => hB _ fun h => hndvd c hc ?_
        rw [← hψ]
        exact orderOf_dvd_of_pow_eq_one h
    _ = (∏ ℓ ∈ T, ((ℓ : ℝ) - 1)) * B := by
        rw [Finset.sum_const, nsmul_eq_mul, Fintype.card_piFinset]
        congr 1
        rw [← Finset.prod_coe_sort T (fun ℓ => ((ℓ : ℝ) - 1))]
        push_cast
        refine Finset.prod_congr rfl fun ℓ _ => ?_
        have h1 : 1 ≤ (ℓ : ℕ) := (Nat.mem_primeFactors.mp (hT ℓ.2)).1.one_lt.le
        rw [Nat.card_Ico, Nat.cast_sub h1, Nat.cast_one]

end Erdos985.Indicator
