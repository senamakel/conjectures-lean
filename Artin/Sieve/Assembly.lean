import Artin.Sieve.KummerInputs
import Artin.Sieve.Density
import Artin.Sieve.HugePrimes
import Artin.Sieve.BrunTitchmarshLargePrimes
import Mathlib.NumberTheory.Primorial

/-!
# Assembling the sieve half (blueprint B1, B2, and the join with B3, B4, B7)

`artin_of_effectiveKummerChebotarev_of_kummer` proves the sieve half of Hooley's argument,
`EffectiveKummerChebotarev a → ∃ δ > 0, (S a).HasDensity δ`, from the two Kummer-theory facts
stated in `Artin/Sieve/KummerInputs.lean`.

Write `N(x) = primRootCount a x`, `L = log x`, `ξ₁ = ⌊L / 6⌋`, `P = ξ₁#` (the product of the
primes `q ≤ ξ₁`), `ξ₂ = √x / L²` and `ξ₃ = √x · L`.

* **B1, small primes.** `M(x) = Σ_{k ∣ P} μ(k) · kummerCount a k x` satisfies `N(x) ≤ M(x)` and
  `M(x) ≤ N(x) + (primes sifted by some q > ξ₁)` (`abs_primRootCount_sub_le`). Effective
  Chebotarev for each `k ∣ P` gives `|M(x) − π(x) Σ_{k ∣ P} μ(k)/[K_k:ℚ]| ≤ P · C√x log(Px)`
  (`abs_sum_moebius_sub_le`). Since `P ≤ 4^{ξ₁} ≤ x^{1/3}`, this is `≪ x^{5/6} L`, so
  `o(π(x))` (`error_ratio_le`). The truncated density `Σ_{k ∣ P} μ(k)/[K_k:ℚ]` tends to
  `δ(a) = Σ_k μ(k)/[K_k:ℚ]` (`tendsto_sum_divisors_primorial`), because the series converges
  absolutely (`summable_moebius_div_kummerDegree`, from `KummerDegreeLowerBound` and
  `n ≤ 2 φ(n)²`).
* **B2, medium primes** `ξ₁ < q ≤ ξ₂`: `kummerCount a q x ≤ c π(x)/(q(q−1)) + 2C√x L`, summed
  over the at most `π(ξ₂) ≪ √x / L³` such primes (Chebyshev), gives
  `≤ c π(x) Σ_{q > ξ₁} 1/(q φ(q)) + O(x / L²) = o(π(x))` (`medium_le`).
* **B3, large primes** `ξ₂ < q ≤ ξ₃`: `largePrimeCount_isLittleO`.
* **B4, huge primes** `q > ξ₃`: `hugePrimeCount_le`, `O(x / L²)`.
* **B7**: `N(x)/π(x) → δ(a)` (`tendsto_primRootCount_div`) and `hasDensity_of_tendsto`.
-/

namespace Artin

open ArtinPrimitiveRootsConjecture Finset Filter Asymptotics
open scoped ArithmeticFunction.Moebius Topology

/-! ### `n ≤ 2 φ(n)²`, and absolute convergence of `Σ μ(k)/[K_k : ℚ]` -/

lemma totient_sq_aux (n : ℕ) :
    n ≤ 2 * Nat.totient n ^ 2 ∧ (n % 2 = 1 → n ≤ Nat.totient n ^ 2) := by
  induction n using Nat.recOnPosPrimePosCoprime with
  | prime_pow p k hp hk =>
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    rw [Nat.totient_prime_pow_succ hp]
    have ht : 1 ≤ p ^ j := Nat.one_le_pow _ _ hp.pos
    rcases hp.eq_two_or_odd' with rfl | hodd
    · refine ⟨?_, fun h => ?_⟩
      · rw [pow_succ]
        norm_num
        nlinarith
      · have : 2 ^ (j + 1) % 2 = 0 := by rw [pow_succ]; simp
        omega
    · have hp3 : 3 ≤ p := by
        obtain ⟨m, hm⟩ := hodd
        have := hp.two_le
        omega
      obtain ⟨r, rfl⟩ : ∃ r, p = r + 1 := ⟨p - 1, by omega⟩
      simp only [Nat.add_sub_cancel]
      have key : (r + 1) ^ (j + 1) ≤ ((r + 1) ^ j * r) ^ 2 := by
        have h1 : r + 1 ≤ r * r := by nlinarith
        calc (r + 1) ^ (j + 1) = (r + 1) ^ j * (r + 1) := pow_succ _ _
          _ ≤ (r + 1) ^ j * (r * r) := Nat.mul_le_mul_left _ h1
          _ ≤ ((r + 1) ^ j * (r + 1) ^ j) * (r * r) :=
              Nat.mul_le_mul_right _ (Nat.le_mul_of_pos_right _ ht)
          _ = ((r + 1) ^ j * r) ^ 2 := by ring
      exact ⟨key.trans (by omega), fun _ => key⟩
  | zero => simp
  | one => simp
  | coprime a b ha hb hab iha ihb =>
    rw [Nat.totient_mul hab, mul_pow]
    have hmod := Nat.mul_mod a b 2
    have hnot : ¬ (a % 2 = 0 ∧ b % 2 = 0) := by
      rintro ⟨h1, h2⟩
      have := Nat.dvd_gcd (Nat.dvd_of_mod_eq_zero h1) (Nat.dvd_of_mod_eq_zero h2)
      rw [Nat.Coprime.gcd_eq_one hab] at this
      exact absurd (Nat.dvd_one.mp this) (by norm_num)
    rcases Nat.mod_two_eq_zero_or_one a with ha2 | ha2 <;>
      rcases Nat.mod_two_eq_zero_or_one b with hb2 | hb2
    · exact absurd ⟨ha2, hb2⟩ hnot
    · refine ⟨?_, fun h => ?_⟩
      · calc a * b ≤ (2 * Nat.totient a ^ 2) * Nat.totient b ^ 2 :=
            Nat.mul_le_mul iha.1 (ihb.2 hb2)
          _ = _ := by ring
      · rw [hmod, ha2] at h; simp at h
    · refine ⟨?_, fun h => ?_⟩
      · calc a * b ≤ Nat.totient a ^ 2 * (2 * Nat.totient b ^ 2) :=
            Nat.mul_le_mul (iha.2 ha2) ihb.1
          _ = _ := by ring
      · rw [hmod, hb2] at h; simp at h
    · have h := Nat.mul_le_mul (iha.2 ha2) (ihb.2 hb2)
      exact ⟨h.trans (by omega), fun _ => h⟩

/-- `n ≤ 2 φ(n)²`, that is `φ(n) ≥ √(n/2)`. -/
lemma le_two_mul_totient_sq (n : ℕ) : n ≤ 2 * Nat.totient n ^ 2 := (totient_sq_aux n).1

/-- `1 / (k φ(k))`. -/
noncomputable def invKTot (k : ℕ) : ℝ := 1 / ((k : ℝ) * Nat.totient k)

lemma invKTot_nonneg (k : ℕ) : 0 ≤ invKTot k := by unfold invKTot; positivity

lemma invKTot_le (k : ℕ) : invKTot k ≤ 2 * ((k : ℝ) ^ (3 / 2 : ℝ))⁻¹ := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp [invKTot]
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have htR : (0 : ℝ) < Nat.totient k := by exact_mod_cast Nat.totient_pos.mpr hk
  have h32 : (k : ℝ) ^ (3 / 2 : ℝ) = k * Real.sqrt k := by
    rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add hkR, Real.rpow_one,
      Real.sqrt_eq_rpow]
  have hcast : (k : ℝ) ≤ 2 * (Nat.totient k : ℝ) ^ 2 := by
    exact_mod_cast le_two_mul_totient_sq k
  have hsq : Real.sqrt k ≤ 2 * Nat.totient k :=
    Real.sqrt_le_iff.mpr ⟨by positivity, by nlinarith⟩
  rw [h32, invKTot, ← div_eq_mul_inv, div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [mul_le_mul_of_nonneg_left hsq hkR.le]

/-- `Σ 1/(k φ(k))` converges. -/
lemma summable_invKTot : Summable invKTot :=
  Summable.of_nonneg_of_le invKTot_nonneg invKTot_le
    ((Real.summable_nat_rpow_inv.mpr (by norm_num)).mul_left 2)

/-- From `KummerDegreeLowerBound`: `[K_k : ℚ] > 0` and `1/[K_k : ℚ] ≤ c/(k φ(k))`. -/
lemma inv_kummerDegree_le {a : ℤ} {c : ℝ} (hc : 0 < c)
    (hK : ∀ k : ℕ, Squarefree k → 0 < k →
      ((k : ℝ) * (Nat.totient k : ℝ)) ≤ c * (kummerDegree a k : ℝ))
    {k : ℕ} (hsq : Squarefree k) (hk : 0 < k) :
    0 < (kummerDegree a k : ℝ) ∧ 1 / (kummerDegree a k : ℝ) ≤ c * invKTot k := by
  have hkt : (0 : ℝ) < k * Nat.totient k := by
    have : (0 : ℝ) < k := by exact_mod_cast hk
    have : (0 : ℝ) < Nat.totient k := by exact_mod_cast Nat.totient_pos.mpr hk
    positivity
  have hD := hK k hsq hk
  have hDpos : (0 : ℝ) < kummerDegree a k := by
    by_contra hneg
    push Not at hneg
    nlinarith
  refine ⟨hDpos, ?_⟩
  rw [invKTot, mul_one_div, div_le_div_iff₀ hDpos hkt]
  linarith

/-- **Absolute convergence of the Artin series**, from `KummerDegreeLowerBound`. -/
theorem summable_moebius_div_kummerDegree (a : ℤ) (hK1 : KummerDegreeLowerBound a) :
    Summable fun k : ℕ => (μ k : ℝ) / (kummerDegree a k : ℝ) := by
  obtain ⟨c, hc, hK⟩ := hK1
  refine Summable.of_norm_bounded (summable_invKTot.mul_left c) fun k => ?_
  rw [Real.norm_eq_abs]
  by_cases hsq : Squarefree k
  · rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp only [ArithmeticFunction.map_zero, Int.cast_zero, zero_div, abs_zero]
      exact mul_nonneg hc.le (invKTot_nonneg 0)
    obtain ⟨hDpos, hle⟩ := inv_kummerDegree_le hc hK hsq hk
    have hmu : |(μ k : ℝ)| ≤ 1 := by exact_mod_cast ArithmeticFunction.abs_moebius_le_one
    rw [abs_div, abs_of_pos hDpos]
    calc |(μ k : ℝ)| / kummerDegree a k ≤ 1 / kummerDegree a k :=
          div_le_div_of_nonneg_right hmu hDpos.le
      _ ≤ c * invKTot k := hle
  · rw [ArithmeticFunction.moebius_eq_zero_of_not_squarefree hsq, Int.cast_zero, zero_div,
      abs_zero]
    exact mul_nonneg hc.le (invKTot_nonneg k)

/-- The tail `Σ_{k ≥ n} 1/(k φ(k))`. -/
noncomputable def tailInvKTot (n : ℕ) : ℝ := ∑' k, invKTot k - ∑ k ∈ range n, invKTot k

lemma tendsto_tailInvKTot : Tendsto tailInvKTot atTop (𝓝 0) := by
  have h := (tendsto_const_nhds (x := ∑' k, invKTot k)).sub
    summable_invKTot.hasSum.tendsto_sum_nat
  rw [sub_self] at h
  exact h

lemma sum_le_tailInvKTot (s : Finset ℕ) (n : ℕ) (hs : ∀ k ∈ s, n ≤ k) :
    ∑ k ∈ s, invKTot k ≤ tailInvKTot n := by
  have hdisj : Disjoint s (range n) := by
    rw [Finset.disjoint_left]
    intro k hk hk'
    have := hs k hk
    rw [mem_range] at hk'
    omega
  have := summable_invKTot.sum_le_tsum (s ∪ range n) (fun k _ => invKTot_nonneg k)
  rw [sum_union hdisj] at this
  unfold tailInvKTot
  linarith

/-- The sum of an absolutely convergent series supported on squarefree `k ≥ 1`, truncated to
`k ∣ ξ#`, tends to the full sum as `ξ → ∞`. -/
lemma tendsto_sum_divisors_primorial {f : ℕ → ℝ} (hf : Summable f)
    (hf0 : ∀ k, ¬ Squarefree k → f k = 0) (hf00 : f 0 = 0) :
    Tendsto (fun ξ : ℕ => ∑ k ∈ (primorial ξ).divisors, f k) atTop (𝓝 (∑' k, f k)) := by
  have hT : Tendsto (fun ξ : ℕ => (primorial ξ).divisors ∪ range ξ) atTop atTop :=
    tendsto_atTop_mono (fun ξ => subset_union_right) tendsto_finset_range
  have hS : Tendsto (fun s : Finset ℕ => ∑ k ∈ s, f k) atTop (𝓝 (∑' k, f k)) := hf.hasSum
  refine (hS.comp hT).congr fun ξ => ?_
  simp only [Function.comp]
  refine (sum_subset subset_union_left fun k hk hk' => ?_).symm
  have hkξ : k < ξ := by
    rcases mem_union.mp hk with h | h
    · exact absurd h hk'
    · exact mem_range.mp h
  rcases Nat.eq_zero_or_pos k with rfl | hk0
  · exact hf00
  by_cases hsq : Squarefree k
  · exfalso
    refine hk' (Nat.mem_divisors.mpr ⟨?_, primorial_ne_zero _⟩)
    exact hsq.dvd_primorial.trans (primorial_dvd_primorial hkξ.le)
  · exact hf0 k hsq

/-! ### The sieve inequalities -/

/-- `ξ₁ = ⌊(1/6) log x⌋`. -/
noncomputable def xi1 (x : ℕ) : ℕ := ⌊Real.log x / 6⌋₊

/-- The medium primes `ξ < q ≤ ξ₂`. -/
noncomputable def medPrimes (ξ x : ℕ) : Finset ℕ := (Ioc ξ ⌊xi2 x⌋₊).filter Nat.Prime

/-- A prime `p < x` that survives the sieve by the primes `q ≤ ξ` but has `a` not a primitive
root is sifted out by a medium, large or huge prime `q > ξ`. -/
theorem siftedCount_le (a : ℤ) (ξ x : ℕ) :
    siftedCount a (Nat.primesLE ξ) x ≤ primRootCount a x +
      ∑ q ∈ medPrimes ξ x, kummerCount a q x + largePrimeCount a x + hugePrimeCount a x := by
  classical
  set A := (range x).filter fun p : ℕ => p.Prime ∧ orderOf (a : ZMod p) = p - 1
  set B := (medPrimes ξ x).biUnion fun q =>
    (range x).filter fun p : ℕ => p.Prime ∧ ¬ (p : ℤ) ∣ a ∧ q ∣ p - 1 ∧
      (a : ZMod p) ^ ((p - 1) / q) = 1
  set Cs := (range x).filter fun p : ℕ => p.Prime ∧ ¬ (p : ℤ) ∣ a ∧
    ∃ q : ℕ, q.Prime ∧ xi2 x < q ∧ (q : ℝ) ≤ xi3 x ∧ q ∣ p - 1 ∧
      (a : ZMod p) ^ ((p - 1) / q) = 1
  set D := (range x).filter fun p : ℕ => p.Prime ∧ ¬ (p : ℤ) ∣ a ∧
    ∃ q : ℕ, q.Prime ∧ Real.sqrt x * Real.log x < q ∧ q ∣ p - 1 ∧
      (a : ZMod p) ^ ((p - 1) / q) = 1
  have key : ((range x).filter fun p : ℕ => p.Prime ∧ ¬ (p : ℤ) ∣ a ∧
      ∀ q ∈ Nat.primesLE ξ, ¬ (q ∣ p - 1 ∧ (a : ZMod p) ^ ((p - 1) / q) = 1)) ⊆
      A ∪ B ∪ Cs ∪ D := by
    intro p hp
    simp only [Finset.mem_filter, Finset.mem_range] at hp
    obtain ⟨hpx, hp, hpa, hsift⟩ := hp
    by_cases hord : orderOf (a : ZMod p) = p - 1
    · refine mem_union_left _ (mem_union_left _ (mem_union_left _ ?_))
      simp [A, hpx, hp, hord]
    · have := mt (orderOf_eq_sub_one_iff hp hpa).mpr hord
      push Not at this
      obtain ⟨q, hq, hqd, heq⟩ := this
      have hqp := Nat.le_of_dvd (Nat.sub_pos_of_lt hp.one_lt) hqd
      have hξq : ξ < q := by
        by_contra hle
        exact hsift q (Nat.mem_primesLE.mpr ⟨by omega, hq⟩) ⟨hqd, heq⟩
      by_cases h2 : (q : ℝ) ≤ xi2 x
      · refine mem_union_left _ (mem_union_left _ (mem_union_right _ ?_))
        simp only [B, medPrimes, mem_biUnion, mem_filter, mem_Ioc, mem_range]
        exact ⟨q, ⟨⟨hξq, Nat.le_floor h2⟩, hq⟩, hpx, hp, hpa, hqd, heq⟩
      · push Not at h2
        by_cases h3 : (q : ℝ) ≤ xi3 x
        · refine mem_union_left _ (mem_union_right _ ?_)
          simp only [Cs, mem_filter, mem_range]
          exact ⟨hpx, hp, hpa, q, hq, h2, h3, hqd, heq⟩
        · push Not at h3
          refine mem_union_right _ ?_
          simp only [D, mem_filter, mem_range]
          exact ⟨hpx, hp, hpa, q, hq, h3, hqd, heq⟩
  have hB : B.card ≤ ∑ q ∈ medPrimes ξ x, kummerCount a q x := by
    refine card_biUnion_le.trans (le_of_eq ?_)
    rfl
  have hC : Cs.card = largePrimeCount a x := by
    rw [largePrimeCount]
  have hD : D.card = hugePrimeCount a x := by
    rw [hugePrimeCount]
  rw [siftedCount]
  calc _ ≤ (A ∪ B ∪ Cs ∪ D).card := card_le_card key
    _ ≤ A.card + B.card + Cs.card + D.card := by
        refine (card_union_le _ _).trans (Nat.add_le_add_right ?_ _)
        refine (card_union_le _ _).trans (Nat.add_le_add_right ?_ _)
        exact card_union_le _ _
    _ ≤ _ := by
        rw [hC, hD]
        have hA : A.card = primRootCount a x := rfl
        omega

/-- **Truncated sieve, both sides (B1).** `|N(x) − Σ_{k ∣ ξ#} μ(k) kummerCount a k x|` is at most
the number of primes sifted out by a medium, large or huge prime `q > ξ`. -/
lemma abs_primRootCount_sub_le (a : ℤ) (ξ x : ℕ) :
    |(primRootCount a x : ℝ) - ∑ k ∈ (primorial ξ).divisors, (μ k : ℝ) * kummerCount a k x| ≤
      (∑ q ∈ medPrimes ξ x, (kummerCount a q x : ℝ)) + largePrimeCount a x +
        hugePrimeCount a x := by
  have h1 := primRootCount_le_sum_moebius a ξ x
  have h2 := sum_moebius_kummerCount a (Nat.primesLE ξ)
    (fun q hq => (Nat.mem_primesLE.mp hq).2) x
  have h3 := siftedCount_le a ξ x
  rw [← primorial_eq_prod_primesLE] at h1 h2
  have h1' : (primRootCount a x : ℝ) ≤
      ∑ k ∈ (primorial ξ).divisors, (μ k : ℝ) * kummerCount a k x := by
    have := (Int.cast_le (R := ℝ)).mpr h1
    push_cast at this
    exact this
  have h2' : ∑ k ∈ (primorial ξ).divisors, (μ k : ℝ) * kummerCount a k x =
      siftedCount a (Nat.primesLE ξ) x := by
    have := congrArg (Int.cast (R := ℝ)) h2
    push_cast at this
    exact this
  have h3' : (siftedCount a (Nat.primesLE ξ) x : ℝ) ≤ primRootCount a x +
      (∑ q ∈ medPrimes ξ x, (kummerCount a q x : ℝ)) + largePrimeCount a x +
        hugePrimeCount a x := by
    exact_mod_cast h3
  have h0 : (0 : ℝ) ≤ (∑ q ∈ medPrimes ξ x, (kummerCount a q x : ℝ)) + largePrimeCount a x +
      hugePrimeCount a x := by positivity
  rw [abs_le]
  constructor <;> linarith

/-- **Effective Chebotarev, summed over `k ∣ P` (B1).** -/
lemma abs_sum_moebius_sub_le (a : ℤ) {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ k x : ℕ, Squarefree k → 2 ≤ x →
      |(kummerCount a k x : ℝ) - (Nat.primeCounting x : ℝ) / kummerDegree a k|
        ≤ C * Real.sqrt x * Real.log (k * x))
    (P x : ℕ) (hP : P ≠ 0) (hx : 2 ≤ x) :
    |∑ k ∈ P.divisors, (μ k : ℝ) * kummerCount a k x -
        (Nat.primeCounting x : ℝ) * ∑ k ∈ P.divisors, (μ k : ℝ) / kummerDegree a k| ≤
      P * (C * Real.sqrt x * Real.log (P * x)) := by
  rw [mul_sum, ← sum_sub_distrib]
  have hxR : (2 : ℝ) ≤ x := by exact_mod_cast hx
  have hPR : (1 : ℝ) ≤ P := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hP
  have hlogP : 0 ≤ Real.log (P * x) := Real.log_nonneg (by nlinarith)
  have hCs : 0 ≤ C * Real.sqrt x := mul_nonneg hC (Real.sqrt_nonneg _)
  calc _ ≤ ∑ k ∈ P.divisors, |(μ k : ℝ) * kummerCount a k x -
          (Nat.primeCounting x : ℝ) * ((μ k : ℝ) / kummerDegree a k)| :=
        abs_sum_le_sum_abs _ _
    _ ≤ ∑ _k ∈ P.divisors, C * Real.sqrt x * Real.log (P * x) := by
        refine sum_le_sum fun k hk => ?_
        have hkP := Nat.divisor_le hk
        have hk0 : 0 < k := Nat.pos_of_mem_divisors hk
        rw [show (μ k : ℝ) * kummerCount a k x -
            (Nat.primeCounting x : ℝ) * ((μ k : ℝ) / kummerDegree a k) =
            (μ k : ℝ) * (kummerCount a k x - (Nat.primeCounting x : ℝ) / kummerDegree a k) by
          ring, abs_mul]
        by_cases hsq : Squarefree k
        · have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk0
          have hkPR : (k : ℝ) ≤ P := by exact_mod_cast hkP
          have hlog : Real.log (k * x) ≤ Real.log (P * x) :=
            Real.log_le_log (by positivity) (by nlinarith)
          have hmu : |(μ k : ℝ)| ≤ 1 := by exact_mod_cast ArithmeticFunction.abs_moebius_le_one
          calc |(μ k : ℝ)| * |(kummerCount a k x : ℝ) -
                (Nat.primeCounting x : ℝ) / kummerDegree a k|
              ≤ 1 * (C * Real.sqrt x * Real.log (k * x)) :=
                mul_le_mul hmu (h k x hsq hx) (abs_nonneg _) zero_le_one
            _ ≤ C * Real.sqrt x * Real.log (P * x) := by
                rw [one_mul]; exact mul_le_mul_of_nonneg_left hlog hCs
        · rw [ArithmeticFunction.moebius_eq_zero_of_not_squarefree hsq, Int.cast_zero,
            abs_zero, zero_mul]
          exact mul_nonneg hCs hlogP
    _ = (P.divisors.card : ℝ) * (C * Real.sqrt x * Real.log (P * x)) := by
        rw [sum_const, nsmul_eq_mul]
    _ ≤ P * (C * Real.sqrt x * Real.log (P * x)) := by
        refine mul_le_mul_of_nonneg_right ?_ (mul_nonneg hCs hlogP)
        exact_mod_cast Nat.card_divisors_le_self P

/-! ### Size estimates -/

lemma primorial_le_four_pow (n : ℕ) : primorial n ≤ 4 ^ n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · exact (primorial_lt_four_pow n hn.ne').le

lemma log_four_lt_two : Real.log 4 < 2 := by
  have h : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
  have := Real.log_two_lt_d9
  linarith

/-- `ξ₁# ≤ 4^{ξ₁} ≤ e^{L/3} = x^{1/3}`. -/
lemma primorial_xi1_le {x : ℕ} (hx : 1 ≤ x) :
    (primorial (xi1 x) : ℝ) ≤ Real.exp (Real.log x / 3) := by
  have hL : 0 ≤ Real.log x := Real.log_nonneg (by exact_mod_cast hx)
  have hξ : (xi1 x : ℝ) ≤ Real.log x / 6 := Nat.floor_le (by positivity)
  have h0 : (0 : ℝ) ≤ xi1 x := Nat.cast_nonneg _
  have h4 := log_four_lt_two
  calc (primorial (xi1 x) : ℝ) ≤ (4 : ℝ) ^ xi1 x := by exact_mod_cast primorial_le_four_pow _
    _ = Real.exp (xi1 x * Real.log 4) := by rw [Real.exp_nat_mul, Real.exp_log (by norm_num)]
    _ ≤ Real.exp (Real.log x / 3) := by
        apply Real.exp_le_exp.mpr
        nlinarith

/-- `Y / π(x) ≤ (2 / log 2) · Y log x / x` for `x ≥ 4` (Chebyshev's lower bound). -/
lemma div_primeCounting_le {x : ℕ} (hx : 4 ≤ x) {Y : ℝ} (hY : 0 ≤ Y) :
    Y / Nat.primeCounting x ≤ 2 / Real.log 2 * Y * Real.log x / x := by
  have hxR : (4 : ℝ) ≤ x := by exact_mod_cast hx
  have h := div_log_le_primeCounting hxR
  rw [Nat.floor_natCast] at h
  have hL : 0 < Real.log x := Real.log_pos (by linarith)
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h' : (x : ℝ) ≤ 2 / Real.log 2 * Nat.primeCounting x * Real.log x := by
    rwa [div_le_iff₀ hL] at h
  have hπ : (0 : ℝ) < Nat.primeCounting x := by
    rcases (Nat.cast_nonneg (α := ℝ) (Nat.primeCounting x)).eq_or_lt with h0 | h0
    · rw [← h0] at h'; simp at h'; linarith
    · exact h0
  rw [div_le_div_iff₀ hπ (by linarith)]
  nlinarith [mul_le_mul_of_nonneg_left h' hY]

/-- **The B1 error term is `o(π(x))`.** -/
lemma error_ratio_le {C : ℝ} (hC : 0 ≤ C) {x : ℕ} (hx : 4 ≤ x) :
    (primorial (xi1 x) : ℝ) * (C * Real.sqrt x * Real.log (primorial (xi1 x) * x)) /
        Nat.primeCounting x ≤
      4 * C / Real.log 2 * (Real.log x ^ 2 * Real.exp (-(Real.log x / 6))) := by
  have hxR : (4 : ℝ) ≤ x := by exact_mod_cast hx
  have hx0 : (0 : ℝ) < x := by linarith
  set L := Real.log x with hLdef
  have hL : 0 < L := Real.log_pos (by linarith)
  have hP := primorial_xi1_le (by omega : 1 ≤ x)
  have hP1 : (1 : ℝ) ≤ primorial (xi1 x) := by exact_mod_cast primorial_pos _
  have hP0 : (0 : ℝ) < primorial (xi1 x) := by linarith
  have hlogP : Real.log (primorial (xi1 x)) ≤ L / 3 := by
    calc _ ≤ Real.log (Real.exp (L / 3)) := Real.log_le_log hP0 hP
      _ = L / 3 := Real.log_exp _
  have hlogPx : Real.log (primorial (xi1 x) * x) ≤ 2 * L := by
    rw [Real.log_mul hP0.ne' hx0.ne']; linarith
  have hlogPx0 : 0 ≤ Real.log (primorial (xi1 x) * x) := Real.log_nonneg (by nlinarith)
  have hsqrt : Real.sqrt x = Real.exp (L / 2) := by
    rw [Real.sqrt_eq_iff_mul_self_eq_of_pos (Real.exp_pos _), ← Real.exp_add, add_halves,
      hLdef, Real.exp_log hx0]
  have hxe : (x : ℝ) = Real.exp L := by rw [hLdef, Real.exp_log hx0]
  have hY : 0 ≤ (primorial (xi1 x) : ℝ) *
      (C * Real.sqrt x * Real.log (primorial (xi1 x) * x)) := by positivity
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine (div_primeCounting_le hx hY).trans ?_
  rw [hsqrt]
  calc 2 / Real.log 2 * ((primorial (xi1 x) : ℝ) *
        (C * Real.exp (L / 2) * Real.log (primorial (xi1 x) * x))) * L / x
      ≤ 2 / Real.log 2 * (Real.exp (L / 3) * (C * Real.exp (L / 2) * (2 * L))) * L / x := by
        gcongr
    _ = 4 * C / Real.log 2 * (L ^ 2 * Real.exp (-(L / 6))) := by
        rw [hxe, show -(L / 6) = L / 3 + L / 2 - L by ring, Real.exp_sub, Real.exp_add]
        field_simp
        ring

lemma tendsto_xi2 : Tendsto xi2 atTop atTop := by
  have h : Tendsto (fun x : ℝ => Real.exp (Real.log x / 4)) atTop atTop :=
    Real.tendsto_exp_atTop.comp (Real.tendsto_log_atTop.atTop_div_const (by norm_num))
  refine tendsto_atTop_mono' atTop ?_ h
  filter_upwards [eventually_ge_atTop (Real.exp 256)] with x hx
  have hpos : 0 < xi2 x := by have := two_le_xi2_of_large hx; linarith
  calc Real.exp (Real.log x / 4) ≤ Real.exp (Real.log (xi2 x)) :=
        Real.exp_le_exp.mpr (log_xi2_of_large hx)
    _ = xi2 x := Real.exp_log hpos

/-- Chebyshev's upper bound at `ξ₂`. -/
lemma eventually_primeCounting_xi2_le : ∀ᶠ x : ℕ in atTop,
    (Nat.primeCounting ⌊xi2 x⌋₊ : ℝ) ≤ (Real.log 4 + 1) * xi2 x / Real.log (xi2 x) :=
  (tendsto_xi2.comp tendsto_natCast_atTop_atTop).eventually
    (Chebyshev.eventually_primeCounting_le one_pos)

/-- **Medium primes (B2).** For `x ≥ e^256` with Chebyshev's bound at `ξ₂`,
`Σ_{ξ < q ≤ ξ₂} kummerCount a q x ≤ c π(x) Σ_{k > ξ} 1/(k φ(k)) + 8 (log 4 + 1) C x / log² x`. -/
lemma medium_le (a : ℤ) {C c : ℝ} (hC : 0 ≤ C) (hc : 0 < c)
    (hK : ∀ k : ℕ, Squarefree k → 0 < k →
      ((k : ℝ) * (Nat.totient k : ℝ)) ≤ c * (kummerDegree a k : ℝ))
    (h : ∀ k x : ℕ, Squarefree k → 2 ≤ x →
      |(kummerCount a k x : ℝ) - (Nat.primeCounting x : ℝ) / kummerDegree a k|
        ≤ C * Real.sqrt x * Real.log (k * x))
    (ξ x : ℕ) (hx : Real.exp 256 ≤ x)
    (hcheb : (Nat.primeCounting ⌊xi2 x⌋₊ : ℝ) ≤ (Real.log 4 + 1) * xi2 x / Real.log (xi2 x)) :
    ∑ q ∈ medPrimes ξ x, (kummerCount a q x : ℝ) ≤
      c * Nat.primeCounting x * tailInvKTot (ξ + 1) +
        8 * (Real.log 4 + 1) * C * x / Real.log x ^ 2 := by
  have hx0 : (0 : ℝ) < x := xpos_of_large hx
  have hLb := log_ge_of_large hx
  set L := Real.log (x : ℝ) with hLdef
  have hL : 0 < L := by linarith
  have hx1 : (1 : ℝ) ≤ x := by
    have := Real.add_one_le_exp 256; linarith
  have hx2 : 2 ≤ x := by
    have : (2 : ℝ) ≤ x := by have := Real.add_one_le_exp 256; linarith
    exact_mod_cast this
  have hxi2pos : 0 < xi2 x := by have := two_le_xi2_of_large hx; linarith
  have hlogxi2 : L / 4 ≤ Real.log (xi2 x) := log_xi2_of_large hx
  have hsx : Real.sqrt x * Real.sqrt x = x := Real.mul_self_sqrt hx0.le
  have hs0 : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx0
  have hxi2x : xi2 x ≤ x := by
    have hsle : Real.sqrt x ≤ x := by nlinarith [Real.sqrt_nonneg (x : ℝ)]
    have : xi2 x ≤ Real.sqrt x := by
      rw [xi2, div_le_iff₀ (by positivity)]
      have h1 : (1 : ℝ) ≤ Real.log (x : ℝ) ^ 2 := by rw [← hLdef]; nlinarith
      nlinarith
    linarith
  have hπ0 : (0 : ℝ) ≤ Nat.primeCounting x := Nat.cast_nonneg _
  -- each term
  have hterm : ∀ q ∈ medPrimes ξ x, (kummerCount a q x : ℝ) ≤
      c * Nat.primeCounting x * invKTot q + 2 * C * Real.sqrt x * L := by
    intro q hq
    simp only [medPrimes, mem_filter, mem_Ioc] at hq
    obtain ⟨⟨-, hq2⟩, hqp⟩ := hq
    have hqR : (q : ℝ) ≤ x := by
      have : (q : ℝ) ≤ ⌊xi2 x⌋₊ := by exact_mod_cast hq2
      linarith [Nat.floor_le hxi2pos.le]
    have hq0 : (0 : ℝ) < q := by exact_mod_cast hqp.pos
    obtain ⟨hDpos, hle⟩ := inv_kummerDegree_le hc hK hqp.squarefree hqp.pos
    have habs := h q x hqp.squarefree hx2
    have hlog : Real.log (q * x) ≤ 2 * L := by
      rw [Real.log_mul hq0.ne' hx0.ne']
      linarith [Real.log_le_log hq0 hqR]
    have h1 : (Nat.primeCounting x : ℝ) / kummerDegree a q ≤
        c * Nat.primeCounting x * invKTot q := by
      rw [div_eq_mul_one_div]
      nlinarith
    have h2 : C * Real.sqrt x * Real.log (q * x) ≤ 2 * C * Real.sqrt x * L := by
      have := mul_le_mul_of_nonneg_left hlog (mul_nonneg hC hs0.le)
      linarith
    have := (abs_le.mp habs).2
    linarith
  have hcard : ((medPrimes ξ x).card : ℝ) ≤ Nat.primeCounting ⌊xi2 x⌋₊ := by
    rw [← Nat.primesLE_card_eq_primeCounting]
    refine Nat.cast_le.mpr (card_le_card fun q hq => ?_)
    simp only [medPrimes, mem_filter, mem_Ioc] at hq
    exact Nat.mem_primesLE.mpr ⟨hq.1.2, hq.2⟩
  have hsum : ∑ q ∈ medPrimes ξ x, invKTot q ≤ tailInvKTot (ξ + 1) := by
    refine sum_le_tailInvKTot _ _ fun q hq => ?_
    simp only [medPrimes, mem_filter, mem_Ioc] at hq
    omega
  have hcount : (Nat.primeCounting ⌊xi2 x⌋₊ : ℝ) ≤ 4 * (Real.log 4 + 1) * Real.sqrt x / L ^ 3 := by
    refine hcheb.trans ?_
    have hl4 : 0 < Real.log 4 + 1 := by positivity
    calc (Real.log 4 + 1) * xi2 x / Real.log (xi2 x)
        ≤ (Real.log 4 + 1) * xi2 x / (L / 4) :=
          div_le_div_of_nonneg_left (by positivity) (by positivity) hlogxi2
      _ = 4 * (Real.log 4 + 1) * Real.sqrt x / L ^ 3 := by
          rw [xi2, ← hLdef]
          field_simp
  calc ∑ q ∈ medPrimes ξ x, (kummerCount a q x : ℝ)
      ≤ ∑ q ∈ medPrimes ξ x, (c * Nat.primeCounting x * invKTot q + 2 * C * Real.sqrt x * L) :=
        sum_le_sum hterm
    _ = c * Nat.primeCounting x * ∑ q ∈ medPrimes ξ x, invKTot q +
          (medPrimes ξ x).card * (2 * C * Real.sqrt x * L) := by
        rw [sum_add_distrib, ← mul_sum, sum_const, nsmul_eq_mul]
    _ ≤ c * Nat.primeCounting x * tailInvKTot (ξ + 1) +
          (4 * (Real.log 4 + 1) * Real.sqrt x / L ^ 3) * (2 * C * Real.sqrt x * L) := by
        gcongr
        exact hcard.trans hcount
    _ = c * Nat.primeCounting x * tailInvKTot (ξ + 1) +
          8 * (Real.log 4 + 1) * C * x / L ^ 2 := by
        have e : (4 * (Real.log 4 + 1) * Real.sqrt x / L ^ 3) * (2 * C * Real.sqrt x * L) =
            8 * (Real.log 4 + 1) * C * (Real.sqrt x * Real.sqrt x) / L ^ 2 := by
          field_simp
          ring
        rw [e, hsx]

/-! ### Assembly -/

/-- The algebra of the final estimate: from `|N − M| ≤ R` and `|M − π S| ≤ E`,
`|N/π − δ| ≤ R/π + E/π + |S − δ|`. -/
lemma abs_div_sub_le {N M π S δ med lg hg E : ℝ} (hπ : 0 < π) (e1 : |N - M| ≤ med + lg + hg)
    (e2 : |M - π * S| ≤ E) :
    |N / π - δ| ≤ med / π + lg / π + hg / π + E / π + |S - δ| := by
  have hsplit : N / π - δ = (N - M) / π + (M - π * S) / π + (S - δ) := by
    field_simp
    ring
  rw [hsplit]
  calc |(N - M) / π + (M - π * S) / π + (S - δ)|
      ≤ |(N - M) / π| + |(M - π * S) / π| + |S - δ| :=
        (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) (le_refl _))
    _ = |N - M| / π + |M - π * S| / π + |S - δ| := by
        rw [abs_div, abs_div, abs_of_pos hπ]
    _ ≤ (med + lg + hg) / π + E / π + |S - δ| := by
        gcongr
    _ = med / π + lg / π + hg / π + E / π + |S - δ| := by
        rw [add_div, add_div]

/-- **`N(x) / π(x) → δ(a)`.** -/
theorem tendsto_primRootCount_div (a : ℤ) (ha : ¬IsSquare a) (ha' : a ≠ -1)
    (hK1 : KummerDegreeLowerBound a) (h : EffectiveKummerChebotarev a) :
    Tendsto (fun x : ℕ => (primRootCount a x : ℝ) / Nat.primeCounting x) atTop
      (𝓝 (∑' k : ℕ, (μ k : ℝ) / (kummerDegree a k : ℝ))) := by
  have ha0 : a ≠ 0 := by rintro rfl; exact ha ⟨0, by simp⟩
  have ha1 : a ≠ 1 := by rintro rfl; exact ha ⟨1, by simp⟩
  have hf : Summable fun k : ℕ => (μ k : ℝ) / (kummerDegree a k : ℝ) :=
    summable_moebius_div_kummerDegree a hK1
  obtain ⟨c, hc, hK⟩ := hK1
  obtain ⟨C, hC⟩ := h
  have hC0 : 0 ≤ C := by
    have h13 := hC 1 3 squarefree_one (by norm_num)
    have hpos : 0 < Real.sqrt ((3 : ℕ) : ℝ) * Real.log ((1 : ℕ) * ((3 : ℕ) : ℝ)) := by
      have : (1 : ℝ) < (1 : ℕ) * ((3 : ℕ) : ℝ) := by norm_num
      have := Real.log_pos this
      positivity
    by_contra hneg
    push Not at hneg
    have : C * Real.sqrt ((3 : ℕ) : ℝ) * Real.log ((1 : ℕ) * ((3 : ℕ) : ℝ)) < 0 := by
      rw [mul_assoc]; exact mul_neg_of_neg_of_pos hneg hpos
    have := (abs_nonneg _).trans h13
    linarith
  set δ := ∑' k : ℕ, (μ k : ℝ) / (kummerDegree a k : ℝ) with hδ
  set f : ℕ → ℝ := fun k => (μ k : ℝ) / (kummerDegree a k : ℝ) with hfdef
  -- `ξ₁ → ∞`
  have hlog : Tendsto (fun x : ℕ => Real.log x) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hξ : Tendsto xi1 atTop atTop :=
    tendsto_nat_floor_atTop.comp (hlog.atTop_div_const (by norm_num))
  -- the truncated density converges
  have hSP : Tendsto (fun x : ℕ => ∑ k ∈ (primorial (xi1 x)).divisors, f k) atTop (𝓝 δ) :=
    (tendsto_sum_divisors_primorial hf
      (fun k hk => by
        simp [hfdef, ArithmeticFunction.moebius_eq_zero_of_not_squarefree hk])
      (by simp [hfdef])).comp hξ
  -- the bound
  set K1 : ℝ := 2 / Real.log 2 * (8 * (Real.log 4 + 1) * C)
  set K2 : ℝ := 2 / Real.log 2 * (a.natAbs + 1 : ℝ)
  set B : ℕ → ℝ := fun x =>
    |∑ k ∈ (primorial (xi1 x)).divisors, f k - δ| +
      4 * C / Real.log 2 * (Real.log x ^ 2 * Real.exp (-(Real.log x / 6))) +
      c * tailInvKTot (xi1 x + 1) + K1 / Real.log x +
      (largePrimeCount a x : ℝ) / Nat.primeCounting x + K2 / Real.log x with hBdef
  have hB : Tendsto B atTop (𝓝 0) := by
    have t1 : Tendsto (fun x : ℕ => |∑ k ∈ (primorial (xi1 x)).divisors, f k - δ|) atTop
        (𝓝 0) := by
      have := (hSP.sub_const δ).abs
      rwa [sub_self, abs_zero] at this
    have t2 : Tendsto (fun x : ℕ => Real.log x ^ 2 * Real.exp (-(Real.log x / 6))) atTop
        (𝓝 0) := by
      have := ((Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 2).comp
        (hlog.atTop_div_const (by norm_num : (0 : ℝ) < 6))).const_mul 36
      rw [mul_zero] at this
      refine this.congr fun x => ?_
      simp only [Function.comp]
      ring
    have t3 : Tendsto (fun x : ℕ => tailInvKTot (xi1 x + 1)) atTop (𝓝 0) :=
      tendsto_tailInvKTot.comp ((tendsto_add_atTop_nat 1).comp hξ)
    have t4 : Tendsto (fun x : ℕ => K1 / Real.log x) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop hlog
    have t5 : Tendsto (fun x : ℕ => (largePrimeCount a x : ℝ) / Nat.primeCounting x) atTop
        (𝓝 0) :=
      (largePrimeCount_isLittleO a).tendsto_div_nhds_zero
    have t6 : Tendsto (fun x : ℕ => K2 / Real.log x) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop hlog
    have := ((((t1.add (t2.const_mul (4 * C / Real.log 2))).add (t3.const_mul c)).add t4).add
      t5).add t6
    simpa using this
  rw [← tendsto_sub_nhds_zero_iff]
  refine squeeze_zero_norm' ?_ hB
  filter_upwards [eventually_ge_atTop ⌈Real.exp 256⌉₊, eventually_primeCounting_xi2_le]
    with x hx hcheb
  have hxe : Real.exp 256 ≤ x := Nat.ceil_le.mp hx
  have hx4R : (4 : ℝ) ≤ x := by have := Real.add_one_le_exp 256; linarith
  have hx4 : 4 ≤ x := by exact_mod_cast hx4R
  have hL : 0 < Real.log x := Real.log_pos (by linarith)
  have hπ : (0 : ℝ) < Nat.primeCounting x := by
    have h' := div_log_le_primeCounting hx4R
    rw [Nat.floor_natCast] at h'
    have : 0 < (x : ℝ) / Real.log x := by positivity
    have hl2 : 0 < 2 / Real.log 2 := div_pos two_pos (Real.log_pos (by norm_num))
    by_contra hneg
    push Not at hneg
    nlinarith
  have e1 := abs_primRootCount_sub_le a (xi1 x) x
  have e2 := abs_sum_moebius_sub_le a hC0 hC (primorial (xi1 x)) x (primorial_ne_zero _)
    (by omega)
  have e3 := error_ratio_le hC0 hx4
  have e4 := medium_le a hC0 hc hK hC (xi1 x) x hxe hcheb
  have e5 := hugePrimeCount_le a ha0 ha1 ha' x (by omega)
  have r4 : (∑ q ∈ medPrimes (xi1 x) x, (kummerCount a q x : ℝ)) / Nat.primeCounting x ≤
      c * tailInvKTot (xi1 x + 1) + K1 / Real.log x := by
    have hY : 0 ≤ 8 * (Real.log 4 + 1) * C * x / Real.log x ^ 2 := by positivity
    have h8 := div_primeCounting_le hx4 hY
    have hsplit : (c * Nat.primeCounting x * tailInvKTot (xi1 x + 1) +
          8 * (Real.log 4 + 1) * C * x / Real.log x ^ 2) / Nat.primeCounting x =
        c * tailInvKTot (xi1 x + 1) +
          (8 * (Real.log 4 + 1) * C * x / Real.log x ^ 2) / Nat.primeCounting x := by
      rw [add_div]; congr 1; field_simp
    have hK1eq : 2 / Real.log 2 * (8 * (Real.log 4 + 1) * C * x / Real.log x ^ 2) *
        Real.log x / x = K1 / Real.log x := by
      have : (x : ℝ) ≠ 0 := by positivity
      simp only [K1]
      field_simp
    have := div_le_div_of_nonneg_right e4 hπ.le
    rw [hsplit] at this
    linarith
  have r5 : (hugePrimeCount a x : ℝ) / Nat.primeCounting x ≤ K2 / Real.log x := by
    have hY : 0 ≤ (a.natAbs + 1 : ℝ) * x / Real.log x ^ 2 := by positivity
    have h8 := div_primeCounting_le hx4 hY
    have hK2eq : 2 / Real.log 2 * ((a.natAbs + 1 : ℝ) * x / Real.log x ^ 2) * Real.log x / x =
        K2 / Real.log x := by
      have : (x : ℝ) ≠ 0 := by positivity
      simp only [K2]
      field_simp
    have := div_le_div_of_nonneg_right e5 hπ.le
    linarith
  have key := abs_div_sub_le (δ := δ) hπ e1 e2
  rw [Real.norm_eq_abs]
  refine key.trans ?_
  simp only [hBdef]
  linarith

/-- **Sieve half, modulo Kummer theory.** Effective Chebotarev for the Kummer fields of `a`,
together with the Kummer-degree facts B5 (`KummerDegreeLowerBound`) and B6 (`KummerDensityPos`),
gives a positive density of primes with `a` as a primitive root: the density is
`δ(a) = Σ_k μ(k)/[K_k : ℚ]`. -/
theorem artin_of_effectiveKummerChebotarev_of_kummer (a : ℤ) (ha : ¬IsSquare a)
    (ha' : a ≠ -1) (hK1 : KummerDegreeLowerBound a) (hK2 : KummerDensityPos a)
    (h : EffectiveKummerChebotarev a) :
    ∃ x > 0, (S a).HasDensity x {p | p.Prime} :=
  ⟨_, hK2, hasDensity_of_tendsto a _ (tendsto_primRootCount_div a ha ha' hK1 h)⟩

end Artin
