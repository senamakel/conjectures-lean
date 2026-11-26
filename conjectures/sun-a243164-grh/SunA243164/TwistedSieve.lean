import Erdos985.Indicator.Lemmas

/-!
# The MTT sieve inequality, twisted by a unit, with a prime-power term

This is `Grosswald.Sieve.principal_le_sieve` (grosswald-grh, MTT Theorem 3) with two changes.

1. **Twist.** The indicator is evaluated at `a · n` for a fixed unit `a` of `ZMod p`. In the
   character expansion `ψ(a n)^k = ψ^k(a) · ψ^k(n)` and `‖ψ^k(a)‖ ≤ 1`, so every non-principal
   weighted sum keeps the bound `B` (`norm_W_le`).
2. **Prime powers.** The hypothesis is only that `a · q` is not a primitive root for primes
   `q < x`. A proper prime power `q^k` may well have `a q^k` primitive, so on those `n` the
   pointwise sieve combination is bounded by `1` instead of `0`. The result therefore carries the
   term `Epp x = Σ_{n < x, n not prime} Λ(n)(1 - n/x)`.

Conclusion (`principal_le_sieve_twisted`): with `F` the prime factors of `p - 1`, `S ⊆ F`,
`E = F \ S`, `δ = 1 - Σ_{ℓ∈S} 1/ℓ > 0`, `θ_E = ∏_{ℓ∈E}(1 - 1/ℓ)`,

`δ θ_E (S₀ - (2^{|E|}(2 + (|S| - 1)/δ) - 1) B) ≤ Epp x`.

The definitions and the proofs follow grosswald-grh's `Grosswald/Sieve.lean` and erdos-985's
`Erdos985/Indicator/Lemmas.lean` (`W`, `norm_W_le`) line by line, with `ψ n` replaced by
`ψ (a * n)`; they are restated here because the twisted forms are not instances of the untwisted
ones.
-/

namespace SunA243164.Sieve

open ArithmeticFunction Finset Erdos985 Erdos985.Indicator

variable (p : ℕ)

/-- `1 - 1/ℓ`. -/
noncomputable def aR (ℓ : ℕ) : ℝ := 1 - 1 / (ℓ : ℝ)

/-- `-1/ℓ`. -/
noncomputable def bR (ℓ : ℕ) : ℝ := -(1 / (ℓ : ℝ))

/-- `Σ_{1 ≤ i < ℓ} ψ(a n)^{i(p-1)/ℓ}`. -/
noncomputable def Aψ (ψ : DirichletCharacter ℂ p) (a : ZMod p) (ℓ n : ℕ) : ℂ :=
  ∑ i ∈ Ico 1 ℓ, ψ (a * n) ^ (i * ((p - 1) / ℓ))

/-- The `ℓ`-th power non-residue indicator at `a n`, written with characters. -/
noncomputable def fac (ψ : DirichletCharacter ℂ p) (a : ZMod p) (ℓ n : ℕ) : ℂ :=
  (bR ℓ : ℂ) * Aψ p ψ a ℓ n + (aR ℓ : ℂ)

/-- Its real value. -/
noncomputable def ind (ψ : DirichletCharacter ℂ p) (a : ZMod p) (ℓ n : ℕ) : ℝ :=
  if ψ (a * n) ^ ((p - 1) / ℓ) = 1 then 0 else 1

/-- The weighted sum of the indicator of `T`-freeness of `a n`. -/
noncomputable def V (ψ : DirichletCharacter ℂ p) (a : ZMod p) (x : ℕ) (T : Finset ℕ) : ℂ :=
  ∑ n ∈ range x, (Λ n : ℂ) * (1 - (n : ℂ) / x) * ∏ ℓ ∈ T, fac p ψ a ℓ n

/-- The twisted weighted sum attached to a set `T` of prime divisors of `p - 1`. -/
noncomputable def W (ψ : DirichletCharacter ℂ p) (a : ZMod p) (x : ℕ) (T : Finset ℕ) : ℂ :=
  ∑ n ∈ range x, (Λ n : ℂ) * (1 - (n : ℂ) / x) * ∏ ℓ ∈ T, Aψ p ψ a ℓ n

/-- Expansion coefficients. -/
noncomputable def coef (T t : Finset ℕ) : ℝ := (∏ ℓ ∈ t, bR ℓ) * ∏ ℓ ∈ T \ t, aR ℓ

/-- `θ_T = ∏_{ℓ ∈ T} (1 - 1/ℓ)`. -/
noncomputable def θ (T : Finset ℕ) : ℝ := ∏ ℓ ∈ T, aR ℓ

/-- The weighted contribution of the proper prime powers below `x`. -/
noncomputable def Epp (x : ℕ) : ℝ :=
  ∑ n ∈ range x, (Λ n : ℝ) * (1 - (n : ℝ) / x) * (if n.Prime then 0 else 1)

lemma prod_fac_expand (ψ : DirichletCharacter ℂ p) (a : ZMod p) (T : Finset ℕ) (n : ℕ) :
    ∏ ℓ ∈ T, fac p ψ a ℓ n = ∑ t ∈ T.powerset, (coef T t : ℂ) * ∏ ℓ ∈ t, Aψ p ψ a ℓ n := by
  unfold fac coef
  rw [Finset.prod_add]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [Finset.prod_mul_distrib]
  push_cast
  ring

lemma V_expand (ψ : DirichletCharacter ℂ p) (a : ZMod p) (x : ℕ) (T : Finset ℕ) :
    V p ψ a x T = ∑ t ∈ T.powerset, (coef T t : ℂ) * W p ψ a x t := by
  unfold V
  simp_rw [prod_fac_expand, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun t _ => ?_
  unfold W
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  ring

lemma aR_pos {ℓ : ℕ} (h : 2 ≤ ℓ) : 0 < aR ℓ := by
  have h2 : (2 : ℝ) ≤ ℓ := by exact_mod_cast h
  simp only [aR]
  rw [sub_pos, div_lt_one (by linarith)]
  linarith

lemma two_le_of_mem {ℓ : ℕ} (h : ℓ ∈ (p - 1).primeFactors) : 2 ≤ ℓ :=
  (Nat.mem_primeFactors.mp h).1.two_le

/-- `|coef T t| · ∏_{t} (ℓ - 1) = θ_T`. -/
lemma abs_coef_mul {T t : Finset ℕ} (hT : ∀ ℓ ∈ T, 2 ≤ ℓ) (htT : t ⊆ T) :
    |coef T t| * (∏ ℓ ∈ t, ((ℓ : ℝ) - 1)) = ∏ ℓ ∈ T, aR ℓ := by
  unfold coef
  rw [abs_mul, Finset.abs_prod, abs_of_nonneg (Finset.prod_nonneg fun ℓ hℓ =>
    (aR_pos (hT ℓ (Finset.sdiff_subset hℓ))).le), mul_comm, ← mul_assoc,
    ← Finset.prod_mul_distrib, ← Finset.prod_sdiff htT, mul_comm]
  congr 1
  refine Finset.prod_congr rfl fun ℓ hℓ => ?_
  have h2 : (2 : ℝ) ≤ ℓ := by exact_mod_cast hT ℓ (htT hℓ)
  simp only [aR, bR, abs_neg]
  rw [abs_of_pos (by positivity)]
  field_simp

variable [Fact p.Prime]

/-- The twisted analogue of `Erdos985.Indicator.norm_W_le`. -/
lemma norm_W_le (ψ : DirichletCharacter ℂ p) (hψ : orderOf ψ = p - 1) (a : ZMod p)
    (x : ℕ) (B : ℝ) (hB : ∀ χ : DirichletCharacter ℂ p, χ ≠ 1 → ‖bachSum χ x‖ ≤ B)
    (T : Finset ℕ) (hT : T ⊆ (p - 1).primeFactors) (hne : T.Nonempty) :
    ‖W p ψ a x T‖ ≤ (∏ ℓ ∈ T, ((ℓ : ℝ) - 1)) * B := by
  classical
  obtain ⟨l, hl⟩ := hne
  set m : (T → ℕ) → ℕ := fun c => ∑ ℓ : T, c ℓ * ((p - 1) / ℓ) with hm
  have hndvd : ∀ c ∈ Fintype.piFinset (fun ℓ : T => Ico 1 (ℓ : ℕ)), ¬ (p - 1) ∣ m c := by
    intro c hc
    rw [Fintype.mem_piFinset] at hc
    refine not_dvd_sum (p - 1) T hT c (fun ℓ => ?_) ⟨l, hl⟩
    have := Finset.mem_Ico.mp (hc ℓ); omega
  have key : ∀ n : ℕ, ∏ ℓ ∈ T, Aψ p ψ a ℓ n =
      ∑ c ∈ Fintype.piFinset (fun ℓ : T => Ico 1 (ℓ : ℕ)), ψ (a * n) ^ m c := by
    intro n
    unfold Aψ
    rw [← Finset.prod_coe_sort, Finset.prod_univ_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [Finset.prod_pow_eq_pow_sum]
  have hB0 : 0 ≤ B := by
    have := hB _ (fun h => by
      have h1 : orderOf ψ ∣ 1 := by rw [h]; exact (orderOf_one (G := DirichletCharacter ℂ p)).le
        |> fun _ => by rw [h, orderOf_one]
      rw [hψ] at h1
      have := (Fact.out : p.Prime).two_le
      have := Nat.le_of_dvd one_pos h1
      omega)
    exact (norm_nonneg _).trans this
  have hW : W p ψ a x T = ∑ c ∈ Fintype.piFinset (fun ℓ : T => Ico 1 (ℓ : ℕ)),
      (ψ ^ m c) a * bachSum (ψ ^ m c) x := by
    unfold W bachSum
    simp_rw [key, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun c hc => Finset.sum_congr rfl fun n _ => ?_
    have hm0 : m c ≠ 0 := fun h => hndvd c hc (h ▸ dvd_zero (p - 1))
    rw [← MulChar.pow_apply' _ hm0, map_mul]
    ring
  rw [hW]
  calc ‖∑ c ∈ Fintype.piFinset (fun ℓ : T => Ico 1 (ℓ : ℕ)), (ψ ^ m c) a * bachSum (ψ ^ m c) x‖
      ≤ ∑ c ∈ Fintype.piFinset (fun ℓ : T => Ico 1 (ℓ : ℕ)),
          ‖(ψ ^ m c) a * bachSum (ψ ^ m c) x‖ := norm_sum_le _ _
    _ ≤ ∑ _c ∈ Fintype.piFinset (fun ℓ : T => Ico 1 (ℓ : ℕ)), B := by
        refine Finset.sum_le_sum fun c hc => ?_
        rw [norm_mul]
        have h1 : ‖(ψ ^ m c) a‖ ≤ 1 := DirichletCharacter.norm_le_one _ _
        have h2 : ‖bachSum (ψ ^ m c) x‖ ≤ B := hB _ fun h => hndvd c hc (by
          rw [← hψ]; exact orderOf_dvd_of_pow_eq_one h)
        calc ‖(ψ ^ m c) a‖ * ‖bachSum (ψ ^ m c) x‖ ≤ 1 * B :=
              mul_le_mul h1 h2 (norm_nonneg _) zero_le_one
          _ = B := one_mul B
    _ = (∏ ℓ ∈ T, ((ℓ : ℝ) - 1)) * B := by
        rw [Finset.sum_const, nsmul_eq_mul, Fintype.card_piFinset]
        congr 1
        rw [← Finset.prod_coe_sort T (fun ℓ => ((ℓ : ℝ) - 1))]
        push_cast
        refine Finset.prod_congr rfl fun ℓ _ => ?_
        have h1 : 1 ≤ (ℓ : ℕ) := (Nat.mem_primeFactors.mp (hT ℓ.2)).1.one_lt.le
        rw [Nat.card_Ico, Nat.cast_sub h1, Nat.cast_one]

/-- Value of `fac` at a unit `a n`. -/
lemma fac_eq (ψ : DirichletCharacter ℂ p) (a : ZMod p) {ℓ : ℕ} (hℓ : ℓ ∈ (p - 1).primeFactors)
    {n : ℕ} (hn : a * (n : ZMod p) ≠ 0) : fac p ψ a ℓ n = (ind p ψ a ℓ n : ℂ) := by
  have h2 := two_le_of_mem p hℓ
  have hdvd : ℓ ∣ p - 1 := (Nat.mem_primeFactors.mp hℓ).2.1
  set ζ := ψ (a * n) ^ ((p - 1) / ℓ) with hζ
  have hA : Aψ p ψ a ℓ n = ∑ i ∈ Ico 1 ℓ, ζ ^ i := by
    simp only [Aψ, hζ]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [pow_mul']
  have hζℓ : ζ ^ ℓ = 1 := by
    rw [hζ, ← pow_mul, Nat.div_mul_cancel hdvd, ← map_pow,
      ZMod.pow_card_sub_one_eq_one hn, map_one]
  have hsplit : ∑ i ∈ range ℓ, ζ ^ i = 1 + ∑ i ∈ Ico 1 ℓ, ζ ^ i := by
    rw [Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot (by omega), pow_zero]
  have hℓ0 : (ℓ : ℂ) ≠ 0 := by exact_mod_cast (by omega : ℓ ≠ 0)
  unfold fac ind
  rw [hA, ← hζ]
  split_ifs with h1
  · rw [h1]
    simp only [one_pow, Finset.sum_const, Nat.card_Ico, nsmul_eq_mul, mul_one, aR, bR]
    rw [Nat.cast_sub (by omega : 1 ≤ ℓ)]
    push_cast
    field_simp
    ring
  · have hgeom : ∑ i ∈ range ℓ, ζ ^ i = 0 := by
      rw [geom_sum_eq h1, hζℓ, sub_self, zero_div]
    have hI : ∑ i ∈ Ico 1 ℓ, ζ ^ i = -1 := by
      rw [hsplit] at hgeom; linear_combination hgeom
    rw [hI]
    simp only [aR, bR]
    push_cast
    ring

omit [Fact p.Prime] in
lemma ind_nonneg (ψ : DirichletCharacter ℂ p) (a : ZMod p) (ℓ n : ℕ) : 0 ≤ ind p ψ a ℓ n := by
  unfold ind; split_ifs <;> norm_num

omit [Fact p.Prime] in
lemma ind_le_one (ψ : DirichletCharacter ℂ p) (a : ZMod p) (ℓ n : ℕ) : ind p ψ a ℓ n ≤ 1 := by
  unfold ind; split_ifs <;> norm_num

/-- `a n` is a unit for `0 < n < p`... used with `Λ n ≠ 0`, `n < x ≤ p`. -/
lemma mul_ne_zero_of_lt (a : ZMod p) (ha : a ≠ 0) {x n : ℕ} (hxp : x ≤ p) (hn : n < x)
    (hΛ : Λ n ≠ 0) : a * (n : ZMod p) ≠ 0 := by
  have hn1 : 1 < n := by
    by_contra h
    interval_cases n <;> simp at hΛ
  refine mul_ne_zero ha ?_
  rw [Ne, ZMod.natCast_eq_zero_iff]
  intro h
  have := Nat.le_of_dvd (by omega) h
  omega

/-- `V T` is real. -/
lemma V_eq_real (ψ : DirichletCharacter ℂ p) (a : ZMod p) (ha : a ≠ 0) (x : ℕ) (hxp : x ≤ p)
    (T : Finset ℕ) (hT : T ⊆ (p - 1).primeFactors) :
    V p ψ a x T = ((∑ n ∈ range x, (Λ n : ℝ) * (1 - (n : ℝ) / x) * ∏ ℓ ∈ T, ind p ψ a ℓ n : ℝ)
      : ℂ) := by
  unfold V
  push_cast
  refine Finset.sum_congr rfl fun n hn => ?_
  by_cases hΛ : Λ n = 0
  · simp [hΛ]
  have hn0 := mul_ne_zero_of_lt p a ha hxp (mem_range.mp hn) hΛ
  congr 1
  exact Finset.prod_congr rfl fun ℓ hℓ => fac_eq p ψ a (hT hℓ) hn0

/-- The pointwise sieve inequality: `≤ 0` at primes, `≤ 1` at proper prime powers. -/
lemma pointwise (ψ : DirichletCharacter ℂ p) (a : ZMod p) (ha : a ≠ 0) (x : ℕ) (hxp : x ≤ p)
    (hno : ∀ q, q.Prime → q < x → orderOf (a * (q : ZMod p)) ≠ p - 1)
    (S : Finset ℕ) {n : ℕ} (hn : n < x) (hΛ : Λ n ≠ 0) :
    ∑ i ∈ S, ∏ ℓ ∈ insert i ((p - 1).primeFactors \ S), ind p ψ a ℓ n
      - ((S.card : ℝ) - 1) * ∏ ℓ ∈ (p - 1).primeFactors \ S, ind p ψ a ℓ n
      ≤ if n.Prime then 0 else 1 := by
  set P := (p - 1).primeFactors
  set E := P \ S
  set IE := ∏ ℓ ∈ E, ind p ψ a ℓ n
  have hIE0 : 0 ≤ IE := Finset.prod_nonneg fun ℓ _ => ind_nonneg p ψ a ℓ n
  have hIE1 : IE ≤ 1 := Finset.prod_le_one (fun ℓ _ => ind_nonneg p ψ a ℓ n)
    (fun ℓ _ => ind_le_one p ψ a ℓ n)
  have hins : ∀ i ∈ S, ∏ ℓ ∈ insert i E, ind p ψ a ℓ n = ind p ψ a i n * IE := by
    intro i hi
    rw [Finset.prod_insert]
    simp [E, hi]
  rw [Finset.sum_congr rfl hins, ← Finset.sum_mul]
  have hsumS : ∑ i ∈ S, ind p ψ a i n ≤ (S.card : ℝ) := by
    calc ∑ i ∈ S, ind p ψ a i n ≤ ∑ _i ∈ S, (1 : ℝ) :=
          Finset.sum_le_sum fun i _ => ind_le_one p ψ a i n
      _ = S.card := by simp
  split_ifs with hprime
  · have hn0 := mul_ne_zero_of_lt p a ha hxp hn hΛ
    have hord := hno n hprime hn
    obtain ⟨ℓ₀, hℓ₀, hpow⟩ := exists_primeFactor_pow_eq_one p hn0 hord
    have hind0 : ind p ψ a ℓ₀ n = 0 := by
      unfold ind
      rw [ite_eq_left_iff.mpr]
      intro h; exact absurd (by rw [← map_pow, hpow, map_one]) h
    by_cases hE : ℓ₀ ∈ E
    · have : IE = 0 := Finset.prod_eq_zero hE hind0
      rw [this]; simp
    · have hS0 : ℓ₀ ∈ S := by
        by_contra h
        exact hE (Finset.mem_sdiff.mpr ⟨hℓ₀, h⟩)
      have hsum : ∑ i ∈ S, ind p ψ a i n ≤ (S.card : ℝ) - 1 := by
        rw [← Finset.add_sum_erase _ _ hS0, hind0, zero_add]
        calc ∑ i ∈ S.erase ℓ₀, ind p ψ a i n ≤ ∑ _i ∈ S.erase ℓ₀, (1 : ℝ) :=
              Finset.sum_le_sum fun i _ => ind_le_one p ψ a i n
          _ = (S.card : ℝ) - 1 := by
              rw [Finset.sum_const, Finset.card_erase_of_mem hS0, nsmul_eq_mul, mul_one,
                Nat.cast_sub (Finset.card_pos.mpr ⟨ℓ₀, hS0⟩)]
              simp
      nlinarith
  · nlinarith

/-- `V E = θ_E S₀ + O(θ_E (2^{|E|} - 1) B)`. -/
lemma norm_V_sub_le (ψ : DirichletCharacter ℂ p) (hψ : orderOf ψ = p - 1) (a : ZMod p) (x : ℕ)
    (B : ℝ) (hB : ∀ χ : DirichletCharacter ℂ p, χ ≠ 1 → ‖bachSum χ x‖ ≤ B)
    (E : Finset ℕ) (hE : E ⊆ (p - 1).primeFactors) :
    ‖V p ψ a x E - ((θ E * ∑ n ∈ range x, (Λ n : ℝ) * (1 - (n : ℝ) / x) : ℝ) : ℂ)‖
      ≤ θ E * ((2 : ℝ) ^ E.card - 1) * B := by
  have hE2 : ∀ ℓ ∈ E, 2 ≤ ℓ := fun ℓ hℓ => two_le_of_mem p (hE hℓ)
  rw [V_expand, ← Finset.add_sum_erase _ _ (Finset.empty_mem_powerset E)]
  have hW0 : W p ψ a x ∅ = ((∑ n ∈ range x, (Λ n : ℝ) * (1 - (n : ℝ) / x) : ℝ) : ℂ) := by
    simp [W]
  have hc0 : coef E ∅ = θ E := by simp [coef, θ]
  rw [hW0, hc0, Complex.ofReal_mul, add_sub_cancel_left]
  refine (norm_sum_le _ _).trans ?_
  have hcard : ((E.powerset.erase ∅).card : ℝ) = (2 : ℝ) ^ E.card - 1 := by
    rw [Finset.card_erase_of_mem (Finset.empty_mem_powerset E), Finset.card_powerset,
      Nat.cast_sub Nat.one_le_two_pow]
    push_cast
    ring
  calc ∑ t ∈ E.powerset.erase ∅, ‖(coef E t : ℂ) * W p ψ a x t‖
      ≤ ∑ _t ∈ E.powerset.erase ∅, θ E * B := by
        refine Finset.sum_le_sum fun t ht => ?_
        have htE : t ⊆ E := Finset.mem_powerset.mp (Finset.mem_of_mem_erase ht)
        have htne : t.Nonempty := Finset.nonempty_iff_ne_empty.mpr (Finset.ne_of_mem_erase ht)
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, θ, ← abs_coef_mul hE2 htE, mul_assoc]
        exact mul_le_mul_of_nonneg_left (norm_W_le p ψ hψ a x B hB t (htE.trans hE) htne)
          (abs_nonneg _)
    _ = θ E * ((2 : ℝ) ^ E.card - 1) * B := by
        rw [Finset.sum_const, nsmul_eq_mul, hcard]; ring

/-- `V (E ∪ {i}) = (1 - 1/i) V E + O((1 - 1/i) θ_E 2^{|E|} B)`. -/
lemma norm_V_insert_sub_le (ψ : DirichletCharacter ℂ p) (hψ : orderOf ψ = p - 1) (a : ZMod p)
    (x : ℕ) (B : ℝ) (hB : ∀ χ : DirichletCharacter ℂ p, χ ≠ 1 → ‖bachSum χ x‖ ≤ B)
    (E : Finset ℕ) (hE : E ⊆ (p - 1).primeFactors) {i : ℕ} (hi : i ∈ (p - 1).primeFactors)
    (hiE : i ∉ E) :
    ‖V p ψ a x (insert i E) - (aR i : ℂ) * V p ψ a x E‖ ≤ aR i * θ E * (2 : ℝ) ^ E.card * B := by
  have hE2 : ∀ ℓ ∈ E, 2 ≤ ℓ := fun ℓ hℓ => two_le_of_mem p (hE hℓ)
  have hi2 : 2 ≤ i := two_le_of_mem p hi
  have h1 : ∀ t ∈ E.powerset, coef (insert i E) t = aR i * coef E t := by
    intro t ht
    have htE := Finset.mem_powerset.mp ht
    have hit : i ∉ t := fun h => hiE (htE h)
    unfold coef
    rw [Finset.insert_sdiff_of_notMem _ hit,
      Finset.prod_insert (fun h => hiE (Finset.sdiff_subset h))]
    ring
  have h2 : ∀ t ∈ E.powerset, coef (insert i E) (insert i t) = bR i * coef E t := by
    intro t ht
    have htE := Finset.mem_powerset.mp ht
    have hit : i ∉ t := fun h => hiE (htE h)
    unfold coef
    rw [Finset.insert_sdiff_insert, Finset.sdiff_insert_of_notMem hiE, Finset.prod_insert hit]
    ring
  rw [V_expand, V_expand, Finset.sum_powerset_insert hiE, Finset.mul_sum]
  have e1 : ∑ t ∈ E.powerset, (coef (insert i E) t : ℂ) * W p ψ a x t
      = ∑ t ∈ E.powerset, (aR i : ℂ) * ((coef E t : ℂ) * W p ψ a x t) :=
    Finset.sum_congr rfl fun t ht => by rw [h1 t ht]; push_cast; ring
  have e2 : ∑ t ∈ E.powerset, (coef (insert i E) (insert i t) : ℂ) * W p ψ a x (insert i t)
      = ∑ t ∈ E.powerset, ((bR i * coef E t : ℝ) : ℂ) * W p ψ a x (insert i t) :=
    Finset.sum_congr rfl fun t ht => by rw [h2 t ht]
  rw [e1, e2, add_sub_cancel_left]
  refine (norm_sum_le _ _).trans ?_
  calc ∑ t ∈ E.powerset, ‖((bR i * coef E t : ℝ) : ℂ) * W p ψ a x (insert i t)‖
      ≤ ∑ _t ∈ E.powerset, aR i * θ E * B := by
        refine Finset.sum_le_sum fun t ht => ?_
        have htE := Finset.mem_powerset.mp ht
        have hit : i ∉ t := fun h => hiE (htE h)
        have hiP : insert i t ⊆ (p - 1).primeFactors := Finset.insert_subset hi (htE.trans hE)
        have hW := norm_W_le p ψ hψ a x B hB (insert i t) hiP (Finset.insert_nonempty i t)
        rw [Finset.prod_insert hit] at hW
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_mul]
        have hc := abs_coef_mul hE2 htE
        have hbi : |bR i| * ((i : ℝ) - 1) = aR i := by
          have : (2 : ℝ) ≤ i := by exact_mod_cast hi2
          simp only [bR, aR, abs_neg]
          rw [abs_of_pos (by positivity)]
          field_simp
        calc |bR i| * |coef E t| * ‖W p ψ a x (insert i t)‖
            ≤ |bR i| * |coef E t| * (((i : ℝ) - 1) * (∏ ℓ ∈ t, ((ℓ : ℝ) - 1)) * B) :=
              mul_le_mul_of_nonneg_left hW (by positivity)
          _ = (|bR i| * ((i : ℝ) - 1)) * (|coef E t| * ∏ ℓ ∈ t, ((ℓ : ℝ) - 1)) * B := by ring
          _ = aR i * θ E * B := by rw [hbi, hc, θ]
    _ = aR i * θ E * (2 : ℝ) ^ E.card * B := by
        rw [Finset.sum_const, nsmul_eq_mul, Finset.card_powerset]; push_cast; ring

/-- **MTT Theorem 3, twisted, with the prime-power term.** If no prime `q < x ≤ p` makes
`a q` a primitive root modulo `p`, then
`δ θ_E (S₀ - (2^{|E|}(2 + (|S| - 1)/δ) - 1) B) ≤ Epp x`. -/
theorem principal_le_sieve_twisted (hp2 : p ≠ 2) (a : ZMod p) (ha : a ≠ 0) (x : ℕ)
    (hxp : x ≤ p) (B : ℝ) (hB : ∀ χ : DirichletCharacter ℂ p, χ ≠ 1 → ‖bachSum χ x‖ ≤ B)
    (hno : ∀ q, q.Prime → q < x → orderOf (a * (q : ZMod p)) ≠ p - 1)
    (S : Finset ℕ) (hS : S ⊆ (p - 1).primeFactors)
    (hδ : 0 < 1 - ∑ ℓ ∈ S, 1 / (ℓ : ℝ)) :
    (1 - ∑ ℓ ∈ S, 1 / (ℓ : ℝ)) * θ ((p - 1).primeFactors \ S) *
      (∑ n ∈ Finset.range x, (Λ n : ℝ) * (1 - (n : ℝ) / x)
        - ((2 : ℝ) ^ ((p - 1).primeFactors.card - S.card)
          * (2 + ((S.card : ℝ) - 1) / (1 - ∑ ℓ ∈ S, 1 / (ℓ : ℝ))) - 1) * B)
      ≤ Epp x := by
  classical
  have _ := hp2
  have hN : p - 1 ≠ 0 := by
    have := (Fact.out : p.Prime).two_le; omega
  obtain ⟨ψ, hψ⟩ : ∃ ψ : MulChar (ZMod p) ℂ, orderOf ψ = p - 1 :=
    MulChar.exists_mulChar_orderOf (ZMod p) (by rw [ZMod.card])
      (Complex.isPrimitiveRoot_exp (p - 1) hN)
  set P := (p - 1).primeFactors with hP
  set E := P \ S with hEdef
  set δ := 1 - ∑ ℓ ∈ S, 1 / (ℓ : ℝ) with hδdef
  set S₀ := ∑ n ∈ Finset.range x, (Λ n : ℝ) * (1 - (n : ℝ) / x) with hS₀
  set k := E.card with hk
  have hEP : E ⊆ P := Finset.sdiff_subset
  have hkc : k = P.card - S.card := by rw [hk, Finset.card_sdiff_of_subset hS]
  have hθpos : 0 < θ E := Finset.prod_pos fun ℓ hℓ => aR_pos (two_le_of_mem p (hEP hℓ))
  set vE := (V p ψ a x E).re with hvE
  set v : ℕ → ℝ := fun i => (V p ψ a x (insert i E)).re with hv
  -- (a) the sieve inequality summed over `n`
  have hsieve : ∑ i ∈ S, v i - ((S.card : ℝ) - 1) * vE ≤ Epp x := by
    have hreal : ∀ T ⊆ P, (V p ψ a x T).re
        = ∑ n ∈ range x, (Λ n : ℝ) * (1 - (n : ℝ) / x) * ∏ ℓ ∈ T, ind p ψ a ℓ n := by
      intro T hT
      rw [V_eq_real p ψ a ha x hxp T hT, Complex.ofReal_re]
    have hins : ∀ i ∈ S, insert i E ⊆ P := fun i hi => Finset.insert_subset (hS hi) hEP
    simp only [hv, hvE]
    rw [Finset.sum_congr rfl fun i hi => hreal _ (hins i hi), hreal E hEP, Finset.sum_comm,
      Finset.mul_sum, ← Finset.sum_sub_distrib, Epp]
    refine Finset.sum_le_sum fun n hn => ?_
    by_cases hΛ : Λ n = 0
    · simp [hΛ]
    have hw : 0 ≤ (Λ n : ℝ) * (1 - (n : ℝ) / x) := by
      have hnx := mem_range.mp hn
      have hx0 : (0 : ℝ) < x := by exact_mod_cast (by omega : 0 < x)
      have : (n : ℝ) / x ≤ 1 := by
        rw [div_le_one hx0]; exact_mod_cast hnx.le
      exact mul_nonneg vonMangoldt_nonneg (by linarith)
    have hpt := pointwise p ψ a ha x hxp hno S (mem_range.mp hn) hΛ
    have : ∑ i ∈ S, (Λ n : ℝ) * (1 - (n : ℝ) / x) * ∏ ℓ ∈ insert i E, ind p ψ a ℓ n
        - ((S.card : ℝ) - 1) * ((Λ n : ℝ) * (1 - (n : ℝ) / x) * ∏ ℓ ∈ E, ind p ψ a ℓ n)
        = ((Λ n : ℝ) * (1 - (n : ℝ) / x)) * (∑ i ∈ S, ∏ ℓ ∈ insert i E, ind p ψ a ℓ n
          - ((S.card : ℝ) - 1) * ∏ ℓ ∈ E, ind p ψ a ℓ n) := by
      rw [mul_sub (_ * _), Finset.mul_sum]; ring
    rw [this]
    exact mul_le_mul_of_nonneg_left hpt hw
  -- (b) lower bound for `vE`
  have hvE_ge : θ E * S₀ - θ E * ((2 : ℝ) ^ k - 1) * B ≤ vE := by
    have h := norm_V_sub_le p ψ hψ a x B hB E hEP
    rw [← hS₀] at h
    have := (Complex.abs_re_le_norm (V p ψ a x E - ((θ E * S₀ : ℝ) : ℂ))).trans h
    rw [Complex.sub_re, Complex.ofReal_re] at this
    have := (abs_le.mp this).1
    linarith
  -- (c) lower bound for `v i`
  have hv_ge : ∀ i ∈ S, aR i * vE - aR i * θ E * (2 : ℝ) ^ k * B ≤ v i := by
    intro i hi
    have hiE : i ∉ E := fun h => (Finset.mem_sdiff.mp h).2 hi
    have h := norm_V_insert_sub_le p ψ hψ a x B hB E hEP (hS hi) hiE
    have := (Complex.abs_re_le_norm _).trans h
    rw [Complex.sub_re, Complex.re_ofReal_mul] at this
    have := (abs_le.mp this).1
    simp only [hv, hvE]
    linarith
  -- (d) combine
  have hsumA : ∑ i ∈ S, aR i = ((S.card : ℝ) - 1) + δ := by
    simp only [aR, hδdef, Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, mul_one]
    ring
  have h1 : ∑ i ∈ S, (aR i * vE - aR i * θ E * (2 : ℝ) ^ k * B) ≤ ∑ i ∈ S, v i :=
    Finset.sum_le_sum hv_ge
  rw [Finset.sum_sub_distrib, ← Finset.sum_mul, ← Finset.sum_mul, ← Finset.sum_mul,
    hsumA] at h1
  have e : δ * θ E * (S₀ - ((2 : ℝ) ^ k * (2 + ((S.card : ℝ) - 1) / δ) - 1) * B)
      = δ * (θ E * S₀ - θ E * ((2 : ℝ) ^ k - 1) * B)
        - (((S.card : ℝ) - 1) + δ) * θ E * (2 : ℝ) ^ k * B := by
    field_simp
    ring
  rw [← hkc, e]
  nlinarith

end SunA243164.Sieve
