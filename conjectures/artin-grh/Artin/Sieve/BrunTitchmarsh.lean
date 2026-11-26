import Artin.Sieve.Selberg.Bounds
import Mathlib.Data.Int.CardIntervalMod
import Mathlib.Data.Nat.Factorization.Induction

/-!
# Brun–Titchmarsh for primes `≡ 1 (mod q)`

For `q ≥ 1` and `x > q`, the number of primes `p ≤ x` with `p ≡ 1 (mod q)` is at most
`20000 · x / (φ(q) · log(x/q))` (`primeCountAP_le`). The constant is not optimised; the classical
value is `2 + o(1)`.

The proof is the Selberg upper-bound sieve, applied to `A = {n ≤ x : n ≡ 1 (mod q)}`, sifted by the
primes `p ≤ z = √(x/q)` that do not divide `q`. The sieve itself (`SelbergSieve.selberg_bound_simple`)
and its bounds are vendored from PrimeNumberTheoremAnd under `Artin/Sieve/Selberg/`. What is new
here is the arithmetic-progression set-up:

* `card_filter_modEq_one_dvd`: for `d` coprime to `q`, the multiples of `d` in `A` are one residue
  class mod `q d` (CRT), so `|R_d| ≤ 2`;
* `sum_inv_coprime_ge`: `∑_{m ≤ N, (m, q) = 1} 1/m ≥ (φ(q)/q) ∑_{m ≤ N} 1/m`, which bounds the
  Selberg sum `S ≥ (φ(q)/q) log(x/q) / 4`.
-/

open Finset Sieve SelbergSieve BoundingSieve
open scoped Nat ArithmeticFunction ArithmeticFunction.zeta ArithmeticFunction.omega

noncomputable section

namespace Artin.BrunTitchmarsh

/-! ### Harmonic sums over integers coprime to `q` -/

/-- `∑_{m ≤ N, (m,q)=1} 1/m ≥ (φ(q)/q) · ∑_{m ≤ N} 1/m`. -/
theorem sum_inv_coprime_ge (q N : ℕ) :
    ((q.totient : ℝ) / q) * ∑ m ∈ Icc 1 N, (m : ℝ)⁻¹ ≤
      ∑ m ∈ (Icc 1 N).filter (fun m => m.Coprime q), (m : ℝ)⁻¹ := by
  induction q using Nat.recOnPrimePow generalizing N with
  | zero =>
    simp only [Nat.totient_zero, CharP.cast_eq_zero, zero_div, zero_mul]
    exact sum_nonneg fun _ _ => by positivity
  | one => simp
  | prime_pow_mul a p n hp hpa hn ih =>
    have ha : a ≠ 0 := by rintro rfl; exact hpa (dvd_zero p)
    have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
    -- `B` is the sum for `a`, `T` its index set
    set T := (Icc 1 N).filter (fun m => m.Coprime a) with hT
    have hsplit : ∑ m ∈ T, (m : ℝ)⁻¹ =
        ∑ m ∈ (Icc 1 N).filter (fun m => m.Coprime (p ^ n * a)), (m : ℝ)⁻¹ +
          ∑ m ∈ T.filter (fun m => p ∣ m), (m : ℝ)⁻¹ := by
      rw [← sum_filter_not_add_sum_filter T (fun m => p ∣ m), hT, filter_filter]
      congr 2
      ext m
      simp only [mem_filter, Nat.coprime_mul_iff_right, Nat.coprime_pow_right_iff hn,
        Nat.coprime_comm (m := p), Nat.Prime.coprime_iff_not_dvd hp]
      tauto
    -- the multiples of `p` contribute at most `B / p`
    have hmult : ∑ m ∈ T.filter (fun m => p ∣ m), (m : ℝ)⁻¹ ≤ (p : ℝ)⁻¹ * ∑ m ∈ T, (m : ℝ)⁻¹ := by
      have hsub : T.filter (fun m => p ∣ m) ⊆ T.image (fun m => p * m) := by
        intro m hm
        simp only [hT, mem_filter, mem_Icc] at hm
        obtain ⟨⟨⟨h1, hN⟩, hcop⟩, k, rfl⟩ := hm
        refine mem_image.mpr ⟨k, ?_, rfl⟩
        simp only [hT, mem_filter, mem_Icc]
        have hk : 1 ≤ k := by
          rcases Nat.eq_zero_or_pos k with h | h
          · rw [h, mul_zero] at h1; omega
          · exact h
        refine ⟨⟨hk, ?_⟩, hcop.coprime_dvd_left (dvd_mul_left k p)⟩
        nlinarith [hp.two_le]
      calc ∑ m ∈ T.filter (fun m => p ∣ m), (m : ℝ)⁻¹
          ≤ ∑ m ∈ T.image (fun m => p * m), (m : ℝ)⁻¹ :=
            sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => by positivity
        _ = ∑ m ∈ T, ((p * m : ℕ) : ℝ)⁻¹ := by
            rw [sum_image]
            intro i _ j _ hij
            exact Nat.eq_of_mul_eq_mul_left hp.pos hij
        _ = (p : ℝ)⁻¹ * ∑ m ∈ T, (m : ℝ)⁻¹ := by
            rw [mul_sum]
            refine sum_congr rfl fun m _ => ?_
            push_cast
            rw [mul_inv]
    have htot : ((p ^ n * a).totient : ℝ) / ((p ^ n * a : ℕ) : ℝ) =
        (1 - (p : ℝ)⁻¹) * ((a.totient : ℝ) / a) := by
      have hcop : (p ^ n).Coprime a :=
        Nat.Coprime.pow_left n ((Nat.Prime.coprime_iff_not_dvd hp).mpr hpa)
      rw [Nat.totient_mul hcop, Nat.totient_prime_pow hp hn]
      have hp1 : (((p - 1 : ℕ)) : ℝ) = p - 1 := by
        rw [Nat.cast_sub hp.one_lt.le]; simp
      have ha0 : (a : ℝ) ≠ 0 := by exact_mod_cast ha
      obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
      push_cast
      rw [hp1]
      field_simp
      ring
    have hB := ih N
    have hH : 0 ≤ ∑ m ∈ Icc 1 N, (m : ℝ)⁻¹ := sum_nonneg fun _ _ => by positivity
    have hpinv : (p : ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by exact_mod_cast hp.one_lt.le)
    rw [htot]
    calc (1 - (p : ℝ)⁻¹) * ((a.totient : ℝ) / a) * ∑ m ∈ Icc 1 N, (m : ℝ)⁻¹
        = (1 - (p : ℝ)⁻¹) * (((a.totient : ℝ) / a) * ∑ m ∈ Icc 1 N, (m : ℝ)⁻¹) := by ring
      _ ≤ (1 - (p : ℝ)⁻¹) * ∑ m ∈ T, (m : ℝ)⁻¹ :=
          mul_le_mul_of_nonneg_left hB (by linarith)
      _ ≤ _ := by linarith

/-! ### The sieve set-up -/

/-- The primes `p ≤ z` with `p ∤ q`. -/
def sievePrimes (q : ℕ) (z : ℝ) : Finset ℕ :=
  (range (⌊z⌋₊ + 1)).filter fun p => p.Prime ∧ ¬ p ∣ q

/-- The product of the primes `p ≤ z` with `p ∤ q`. -/
def sieveProd (q : ℕ) (z : ℝ) : ℕ := ∏ p ∈ sievePrimes q z, p

lemma sieveProd_squarefree (q : ℕ) (z : ℝ) : Squarefree (sieveProd q z) :=
  prodDistinctPrimes_squarefree _ fun _ hp => (mem_filter.mp hp).2.1

lemma coprime_sieveProd (q : ℕ) (z : ℝ) : (sieveProd q z).Coprime q :=
  Nat.Coprime.prod_left fun _ hp =>
    (Nat.Prime.coprime_iff_not_dvd (mem_filter.mp hp).2.1).mpr (mem_filter.mp hp).2.2

lemma dvd_sieveProd {q p : ℕ} {z : ℝ} (hp : p.Prime) (hpz : (p : ℝ) ≤ z) (hpq : ¬ p ∣ q) :
    p ∣ sieveProd q z := by
  apply dvd_prod_of_mem
  simp only [sievePrimes, mem_filter, mem_range]
  refine ⟨Nat.lt_succ_of_le (Nat.le_floor hpz), hp, hpq⟩

lemma coprime_sieveProd_of_lt {q p : ℕ} {z : ℝ} (hp : p.Prime) (hpz : ⌊z⌋₊ < p) :
    (sieveProd q z).Coprime p :=
  Nat.Coprime.prod_left fun r hr => by
    simp only [sievePrimes, mem_filter, mem_range] at hr
    exact (Nat.coprime_primes hr.2.1 hp).mpr (by omega)

/-- The Selberg sieve for `{n ≤ x : n ≡ 1 (mod q)}`, sifted by the primes `p ≤ z`, `p ∤ q`, with
level `z`, density `ν(d) = 1/d` and total mass `x/q`. -/
def apSieve (q : ℕ) (x z : ℝ) (hz : 1 ≤ z) : SelbergSieve where
  support := (range (⌊x⌋₊ + 1)).filter (· ≡ 1 [MOD q])
  prodPrimes := sieveProd q z
  prodPrimes_squarefree := sieveProd_squarefree q z
  weights := fun _ => 1
  weights_nonneg := fun _ => zero_le_one
  totalMass := x / q
  nu := (ζ : ArithmeticFunction ℝ).pdiv .id
  nu_mult := by arith_mult
  nu_pos_of_prime := fun p hp _ => by
    simp [ite_eq_right hp.ne_zero, Nat.pos_of_ne_zero hp.ne_zero]
  nu_lt_one_of_prime := fun p hp _ => by
    simp only [ArithmeticFunction.pdiv_apply, ArithmeticFunction.natCoe_apply,
      ArithmeticFunction.zeta_apply, hp.ne_zero, ↓reduceIte, Nat.cast_one,
      ArithmeticFunction.id_apply, one_div]
    apply inv_lt_one_of_one_lt₀
    exact_mod_cast hp.one_lt
  level := z
  one_le_level := hz

lemma apSieve_nu_apply {d : ℕ} (hd : d ≠ 0) :
    ((ζ : ArithmeticFunction ℝ).pdiv .id) d = (d : ℝ)⁻¹ := by
  simp [hd]

/-- The multiples of `d` in `{n < M : n ≡ 1 (mod q)}`, for `d` coprime to `q`, form one residue
class mod `q d`, so there are `M / (q d)` or `M / (q d) + 1` of them. -/
lemma card_filter_modEq_one_dvd (q d M : ℕ) (hq : 0 < q) (hd : 0 < d) (hcop : q.Coprime d) :
    ∃ e : ℕ, e ≤ 1 ∧
      ((range M).filter (fun n => n ≡ 1 [MOD q] ∧ d ∣ n)).card = M / (q * d) + e := by
  have hcrt := (Nat.chineseRemainder hcop 1 0).prop
  set c := (Nat.chineseRemainder hcop 1 0 : ℕ)
  have hset : (range M).filter (fun n => n ≡ 1 [MOD q] ∧ d ∣ n) =
      (range M).filter (· ≡ c [MOD q * d]) := by
    ext n
    simp only [mem_filter]
    constructor
    · rintro ⟨h1, h2, h3⟩
      exact ⟨h1, Nat.chineseRemainder_modEq_unique hcop h2 (Nat.modEq_zero_iff_dvd.mpr h3)⟩
    · rintro ⟨h1, h2⟩
      exact ⟨h1, (h2.of_mul_right d).trans hcrt.1,
        Nat.modEq_zero_iff_dvd.mp ((h2.of_mul_left q).trans hcrt.2)⟩
  rw [hset, ← Nat.count_eq_card_filter_range, Nat.count_modEq_card _ (Nat.mul_pos hq hd)]
  exact ⟨_, by split_ifs <;> simp, rfl⟩

lemma abs_rem_apSieve_le (q : ℕ) (hq : 0 < q) (x z : ℝ) (hx : 0 ≤ x) (hz : 1 ≤ z) {d : ℕ}
    (hd : d ∈ (sieveProd q z).divisors) :
    |rem (s := (apSieve q x z hz).toBoundingSieve) d| ≤ 2 := by
  have hd0 : d ≠ 0 := Nat.ne_of_gt (Nat.pos_of_mem_divisors hd)
  have hcop : q.Coprime d :=
    ((coprime_sieveProd q z).coprime_dvd_left (Nat.dvd_of_mem_divisors hd)).symm
  obtain ⟨e, he, hcard⟩ := card_filter_modEq_one_dvd q d (⌊x⌋₊ + 1) hq (Nat.pos_of_ne_zero hd0) hcop
  have hmult : multSum (s := (apSieve q x z hz).toBoundingSieve) d =
      (((⌊x⌋₊ + 1) / (q * d) + e : ℕ) : ℝ) := by
    rw [← hcard]
    simp only [multSum, apSieve, sum_filter, ← sum_boole]
    refine sum_congr rfl fun n _ => ?_
    by_cases h1 : n ≡ 1 [MOD q] <;> by_cases h2 : d ∣ n <;> simp [h1, h2]
  rw [rem, hmult]
  simp only [apSieve, apSieve_nu_apply hd0]
  set M := ⌊x⌋₊ + 1
  set r := M / (q * d)
  set D : ℝ := (q : ℝ) * d
  have hD1 : (1 : ℝ) ≤ D := by
    have : 1 ≤ q * d := Nat.mul_pos hq (Nat.pos_of_ne_zero hd0)
    simp only [D]; exact_mod_cast this
  have hD : (0 : ℝ) < D := by linarith
  have hdiv := Nat.div_add_mod M (q * d)
  have hmod := Nat.mod_lt M (Nat.mul_pos hq (Nat.pos_of_ne_zero hd0))
  have hMR : (M : ℝ) = D * r + ((M % (q * d) : ℕ) : ℝ) := by
    simp only [D, r]; exact_mod_cast hdiv.symm
  have hmodR : ((M % (q * d) : ℕ) : ℝ) < D := by simp only [D]; exact_mod_cast hmod
  have hmod0 : (0 : ℝ) ≤ ((M % (q * d) : ℕ) : ℝ) := Nat.cast_nonneg _
  have hxM : x < M := by simp only [M]; push_cast; exact Nat.lt_floor_add_one x
  have hMx : (M : ℝ) ≤ x + 1 := by simp only [M]; push_cast; linarith [Nat.floor_le hx]
  have heq : (d : ℝ)⁻¹ * (x / q) = x / D := by
    simp only [D]; field_simp
  rw [heq]
  have hlo : (r : ℝ) - 1 ≤ x / D := by
    rw [le_div_iff₀ hD]; nlinarith
  have hhi : x / D ≤ r + 1 := by
    rw [div_le_iff₀ hD]; nlinarith
  have he' : (e : ℝ) ≤ 1 := by exact_mod_cast he
  have he0 : (0 : ℝ) ≤ e := Nat.cast_nonneg e
  push_cast
  rw [abs_le]
  constructor <;> linarith

/-! ### The Brun–Titchmarsh bound -/

/-- The number of primes `p ≤ x` with `p ≡ 1 (mod q)`. -/
def primeCountAP (q : ℕ) (x : ℝ) : ℕ :=
  ((range (⌊x⌋₊ + 1)).filter fun p => p.Prime ∧ p ≡ 1 [MOD q]).card

/-- `1 + log t ≤ 9 t^{1/8}`, so `(1 + log t)^4 ≤ 6561 √t`, for `t ≥ 1`. -/
lemma one_add_log_pow_four_le {t : ℝ} (ht : 1 ≤ t) :
    (1 + Real.log t) ^ 4 ≤ 6561 * Real.sqrt t := by
  have ht0 : 0 ≤ t := by linarith
  have h8 : Real.log t ≤ t ^ (1 / 8 : ℝ) / (1 / 8) := Real.log_le_rpow_div ht0 (by norm_num)
  have h1 : 1 ≤ t ^ (1 / 8 : ℝ) := Real.one_le_rpow ht (by norm_num)
  have hlog : 0 ≤ Real.log t := Real.log_nonneg ht
  have h9 : 1 + Real.log t ≤ 9 * t ^ (1 / 8 : ℝ) := by linarith
  have hpow : (t ^ (1 / 8 : ℝ)) ^ 4 = Real.sqrt t := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul ht0]
    norm_num
  calc (1 + Real.log t) ^ 4 ≤ (9 * t ^ (1 / 8 : ℝ)) ^ 4 := by
        gcongr
    _ = 6561 * Real.sqrt t := by rw [mul_pow, hpow]; norm_num

/-- **Brun–Titchmarsh** for the progression `1 mod q`: for `q ≥ 1` and `x > q`,
`π(x; q, 1) ≤ 20000 · x / (φ(q) log(x/q))`. -/
theorem primeCountAP_le (q : ℕ) (hq : 1 ≤ q) (x : ℝ) (hqx : (q : ℝ) < x) :
    (primeCountAP q x : ℝ) ≤ 20000 * x / (q.totient * Real.log (x / q)) := by
  classical
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have hx0 : 0 < x := by linarith
  set t := x / q with ht_def
  have ht1 : 1 < t := by rw [ht_def, lt_div_iff₀ hq0]; linarith
  have hlogt : 0 < Real.log t := Real.log_pos ht1
  set z := Real.sqrt t with hz_def
  have hz1 : 1 ≤ z := by rw [hz_def, Real.one_le_sqrt]; linarith
  have hlogz : Real.log z = Real.log t / 2 := by
    rw [hz_def, Real.log_sqrt (by linarith)]
  have hphi : (0 : ℝ) < q.totient := by exact_mod_cast Nat.totient_pos.mpr hq
  have hphiq : (q.totient : ℝ) ≤ q := by exact_mod_cast Nat.totient_le q
  set s := apSieve q x z hz1 with hs
  -- Step 1: primes ≤ x in the progression are sifted elements or primes ≤ z
  have h1 : (primeCountAP q x : ℝ) ≤ siftedSum (s := s.toBoundingSieve) + z := by
    have hsift : siftedSum (s := s.toBoundingSieve) =
        (((range (⌊x⌋₊ + 1)).filter (· ≡ 1 [MOD q])).filter
          (fun n => (sieveProd q z).Coprime n)).card := by
      simp only [siftedSum, hs, apSieve]
      rw [← sum_boole, sum_filter]
    have hsub : (range (⌊x⌋₊ + 1)).filter (fun p => p.Prime ∧ p ≡ 1 [MOD q]) ⊆
        (((range (⌊x⌋₊ + 1)).filter (· ≡ 1 [MOD q])).filter
          (fun n => (sieveProd q z).Coprime n)) ∪ Icc 1 ⌊z⌋₊ := by
      intro p hp
      simp only [mem_filter] at hp
      obtain ⟨hpx, hp, hp1⟩ := hp
      rw [mem_union]
      by_cases hpz : p ≤ ⌊z⌋₊
      · right; exact mem_Icc.mpr ⟨hp.one_lt.le, hpz⟩
      · left
        simp only [mem_filter]
        exact ⟨⟨hpx, hp1⟩, coprime_sieveProd_of_lt hp (by omega)⟩
    rw [hsift, primeCountAP]
    calc (((range (⌊x⌋₊ + 1)).filter (fun p => p.Prime ∧ p ≡ 1 [MOD q])).card : ℝ)
        ≤ ((((range (⌊x⌋₊ + 1)).filter (· ≡ 1 [MOD q])).filter
          (fun n => (sieveProd q z).Coprime n)) ∪ Icc 1 ⌊z⌋₊).card := by
          exact_mod_cast card_le_card hsub
      _ ≤ ((((range (⌊x⌋₊ + 1)).filter (· ≡ 1 [MOD q])).filter
          (fun n => (sieveProd q z).Coprime n)).card : ℝ) + (Icc 1 ⌊z⌋₊).card := by
          exact_mod_cast card_union_le _ _
      _ ≤ _ := by
          gcongr
          rw [Nat.card_Icc, Nat.add_sub_cancel]
          exact Nat.floor_le (by linarith)
  -- Step 2: the Selberg bound
  have h2 := SelbergSieve.selberg_bound_simple s
  -- Step 3: the error term
  have h3 : ∑ d ∈ Nat.divisors (s.prodPrimes), (if (d : ℝ) ≤ s.level then
      (3 : ℝ) ^ ω d * |rem (s := s.toBoundingSieve) d| else 0) ≤ 2 * z * (1 + Real.log z) ^ 3 :=
    rem_sum_le_of_const_of_dvd s 2 fun d hd => abs_rem_apSieve_le q hq x z hx0.le hz1 hd
  -- Step 4: the main term
  have hnu_eq : s.nu = (ζ : ArithmeticFunction ℝ).pdiv .id := rfl
  have h4 : ((q.totient : ℝ) / q) * (Real.log t / 4) ≤ s.selbergBoundingSum := by
    have hS := selbergBoundingSum_ge_sum_div_coprime s q
      (fun p hp hpz hpq => dvd_sieveProd hp hpz hpq)
      (by rw [hnu_eq]; exact CompletelyMultiplicative.zeta.pdiv CompletelyMultiplicative.id)
      (fun n => by
        rw [hnu_eq]
        by_cases h : n = 0 <;> simp [h])
      (fun p hp _ => s.nu_lt_one_of_prime p hp (by assumption))
    have hlev : s.level = z := rfl
    rw [hlev] at hS
    have hsqz : 1 ≤ Real.sqrt z := by rw [Real.one_le_sqrt]; exact hz1
    have hsum : ∑ m ∈ (Icc 1 ⌊Real.sqrt z⌋₊).filter (fun m => m.Coprime q), s.nu m =
        ∑ m ∈ (Icc 1 ⌊Real.sqrt z⌋₊).filter (fun m => m.Coprime q), (m : ℝ)⁻¹ := by
      refine sum_congr rfl fun m hm => ?_
      have : m ≠ 0 := by
        simp only [mem_filter, mem_Icc] at hm; omega
      rw [hnu_eq, apSieve_nu_apply this]
    have hlog := Aux.log_le_sum_inv (Real.sqrt z) hsqz
    have hlogsq : Real.log (Real.sqrt z) = Real.log t / 4 := by
      rw [Real.log_sqrt (by linarith), hlogz]; ring
    have hcop := sum_inv_coprime_ge q ⌊Real.sqrt z⌋₊
    have hfrac : 0 ≤ (q.totient : ℝ) / q := by positivity
    calc ((q.totient : ℝ) / q) * (Real.log t / 4)
        = ((q.totient : ℝ) / q) * Real.log (Real.sqrt z) := by rw [hlogsq]
      _ ≤ ((q.totient : ℝ) / q) * ∑ d ∈ Icc 1 ⌊Real.sqrt z⌋₊, (d : ℝ)⁻¹ :=
          mul_le_mul_of_nonneg_left hlog hfrac
      _ ≤ _ := hcop
      _ = _ := hsum.symm
      _ ≤ _ := hS
  have hX : s.totalMass = x / q := rfl
  have h5 : s.totalMass / s.selbergBoundingSum ≤ 4 * x / (q.totient * Real.log t) := by
    rw [hX]
    have hpos : 0 < ((q.totient : ℝ) / q) * (Real.log t / 4) := by positivity
    calc x / q / s.selbergBoundingSum ≤ x / q / (((q.totient : ℝ) / q) * (Real.log t / 4)) :=
          div_le_div_of_nonneg_left (by positivity) hpos h4
      _ = 4 * x / (q.totient * Real.log t) := by
          field_simp
  -- Step 5: the error terms are `≪ t / log t ≤ x / (φ(q) log t)`
  have h6 : 2 * z * (1 + Real.log z) ^ 3 + z ≤ 19683 * x / (q.totient * Real.log t) := by
    have hlz : Real.log z ≤ Real.log t := by rw [hlogz]; linarith
    have hlz0 : 0 ≤ Real.log z := Real.log_nonneg hz1
    have hA : 1 ≤ (1 + Real.log z) ^ 3 := one_le_pow₀ (by linarith)
    have hz0 : 0 ≤ z := by linarith
    have hstep : 2 * z * (1 + Real.log z) ^ 3 + z ≤ 3 * z * (1 + Real.log t) ^ 3 := by
      have : (1 + Real.log z) ^ 3 ≤ (1 + Real.log t) ^ 3 := by gcongr
      nlinarith
    have hzz : z * z = t := Real.mul_self_sqrt (by linarith)
    have hkey : 3 * z * (1 + Real.log t) ^ 3 * Real.log t ≤ 19683 * t := by
      have h4' := one_add_log_pow_four_le ht1.le
      have hB : (1 + Real.log t) ^ 3 * Real.log t ≤ (1 + Real.log t) ^ 4 := by
        rw [pow_succ]
        have : 0 ≤ (1 + Real.log t) ^ 3 := by positivity
        nlinarith
      calc 3 * z * (1 + Real.log t) ^ 3 * Real.log t
          = 3 * z * ((1 + Real.log t) ^ 3 * Real.log t) := by ring
        _ ≤ 3 * z * (6561 * z) :=
            mul_le_mul_of_nonneg_left (hB.trans h4') (by positivity)
        _ = 19683 * t := by rw [← hzz]; ring
    have htx : 19683 * t / Real.log t ≤ 19683 * x / (q.totient * Real.log t) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      have hxq : x / q * q.totient ≤ x := by
        rw [div_mul_eq_mul_div, div_le_iff₀ hq0]; nlinarith
      have h19 : 0 ≤ 19683 * Real.log t := by positivity
      rw [ht_def] at h19 ⊢
      nlinarith [mul_le_mul_of_nonneg_right hxq h19]
    calc 2 * z * (1 + Real.log z) ^ 3 + z ≤ 3 * z * (1 + Real.log t) ^ 3 := hstep
      _ ≤ 19683 * t / Real.log t := by rw [le_div_iff₀ hlogt]; exact hkey
      _ ≤ _ := htx
  calc (primeCountAP q x : ℝ) ≤ siftedSum (s := s.toBoundingSieve) + z := h1
    _ ≤ s.totalMass / s.selbergBoundingSum + 2 * z * (1 + Real.log z) ^ 3 + z := by
        have : s.level = z := rfl
        simp only [this] at h2 h3
        linarith
    _ ≤ 4 * x / (q.totient * Real.log t) + 19683 * x / (q.totient * Real.log t) := by
        linarith
    _ ≤ 20000 * x / (q.totient * Real.log t) := by
        rw [← add_div]
        gcongr
        linarith

end Artin.BrunTitchmarsh
