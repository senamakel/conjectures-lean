import Mathlib

/-!
# Prime-gap conjectures imply Erdős Problem 382 (i)

Erdős Problem 382 (i) asks: if the largest prime factor of `∏_{u ≤ m ≤ v} m` divides it at least
twice, is `v - u = v^{o(1)}`? Cambie observed (quoted in the formal-conjectures docstring, and at
[erdosproblems.com/382](https://www.erdosproblems.com/382)) that it follows from Cramér's
conjecture. The argument:

1. `v < 2u` (formal-conjectures' `lt_two_mul_of_largestPrimeRepeated`), and in fact `[u, v]`
   contains no prime: a prime `q ∈ [u, v]` has `2q > v`, so the largest prime `p ≥ q` of the
   product has `2p > v` and divides exactly one factor, once.
2. So `[u, v]` lies strictly between two consecutive primes `p_m < u ≤ v < p_{m+1}`, and
   `v - u < p_{m+1} - p_m`.
3. Any bound `p_{m+1} - p_m ≤ p_m^ε` (for each `ε > 0`, eventually) gives `v - u ≤ v^ε`.

We prove step 3 from `SubpowerGaps` (that hypothesis, stated here), and derive `SubpowerGaps`
from Cramér's conjecture, Cramér's conjecture from its strict numerical form, and Cramér's
conjecture from Firoozbakht's conjecture (via Chebyshev's lower bound `π(x) log x ≥ x log 2`).

Every premise and the target are copied word for word from google-deepmind/formal-conjectures at
commit `9097e2f`, with the source file and declaration named at each definition.
-/

open Filter

set_option linter.dupNamespace false

namespace Implications.PrimeGaps

/-! ## Definitions copied from formal-conjectures (commit `9097e2f`) -/

namespace Nat

/-- Copied verbatim from formal-conjectures `FormalConjecturesForMathlib/Data/Nat/MaxPrimeFac.lean`,
`Nat.maxPrimeFac` (commit `9097e2f`).

The greatest prime divisor of a natural number `n > 1`.

Takes the junk value `0` for `n = 0` and `1` for `n = 1`. -/
def maxPrimeFac (n : ℕ) : ℕ := if n = 1 then 1 else n.primeFactorsList.getLastI

end Nat

/-- Copied verbatim from formal-conjectures `FormalConjecturesForMathlib/NumberTheory/PrimeGap.lean`,
`primeGap` (commit `9097e2f`).

The prime gap: the difference between the $n+1$-th and $n$-th prime. -/
noncomputable def primeGap (n : ℕ) : ℕ := (n + 1).nth Nat.Prime - n.nth Nat.Prime

namespace Erdos382

/-- Copied verbatim from formal-conjectures `FormalConjectures/ErdosProblems/382.lean`,
`Erdos382.LargestPrimeRepeated` (commit `9097e2f`).

`LargestPrimeRepeated u v` means that $1 \leq u \leq v$ and the largest prime $p$ dividing
$\prod_{u \leq m \leq v} m$ appears in it with exponent at least $2$, that is $p^2$ divides the
product. -/
def LargestPrimeRepeated (u v : ℕ) : Prop :=
  1 ≤ u ∧ u ≤ v ∧ 2 ≤ v ∧
    Nat.maxPrimeFac (∏ m ∈ Finset.Icc u v, m) ^ 2 ∣ ∏ m ∈ Finset.Icc u v, m

/-- The statement of formal-conjectures `FormalConjectures/ErdosProblems/382.lean`,
`Erdos382.erdos_382.parts.i` (commit `9097e2f`, `research open`), copied verbatim as a `Prop`.

For every $\epsilon > 0$, every pair with `LargestPrimeRepeated u v` and $v$ large enough
satisfies $v - u \leq v^{\epsilon}$. -/
def Erdos382PartI : Prop :=
    ∀ ε > (0 : ℝ), ∀ᶠ v : ℕ in atTop, ∀ u : ℕ, LargestPrimeRepeated u v →
      ((v - u : ℕ) : ℝ) ≤ (v : ℝ) ^ ε

end Erdos382

namespace CramerConjecture

/-- Copied verbatim from formal-conjectures `FormalConjectures/Wikipedia/CramerConjecture.lean`,
`CramerConjecture.cramerRatio` (commit `9097e2f`).

Cramér's normalized prime-gap ratio $\dfrac{p_{n+1} - p_n}{(\log p_n)^2}$. -/
noncomputable def cramerRatio (n : ℕ) : ℝ :=
  (primeGap n : ℝ) / (Real.log (Nat.nth Nat.Prime n)) ^ 2

/-- The statement of formal-conjectures `FormalConjectures/Wikipedia/CramerConjecture.lean`,
`CramerConjecture.cramer_conjecture` (commit `9097e2f`, `research open`), copied verbatim as a
`Prop`.

**Cramér's Conjecture**: $p_{n+1} - p_n = O((\log p_n)^2)$ as $n \to \infty$. -/
def CramerConjecture : Prop :=
    (fun n : ℕ => (primeGap n : ℝ)) =O[Filter.atTop]
      (fun n : ℕ => (Real.log (Nat.nth Nat.Prime n)) ^ 2)

/-- The statement of formal-conjectures `FormalConjectures/Wikipedia/CramerConjecture.lean`,
`CramerConjecture.cramer_conjecture.variants.strict_bound` (commit `9097e2f`, `research open`),
copied verbatim as a `Prop` (its binders `(n : ℕ) (hn : 4 ≤ n)` become `∀`).

**Strong Numerical Cramér Inequality**: for every $n \ge 4$, $p_{n+1} - p_n < (\log p_n)^2$. -/
def StrictBound : Prop :=
    ∀ (n : ℕ) (_hn : 4 ≤ n), cramerRatio n < 1

end CramerConjecture

namespace Firoozbakht

open Real

/-- Copied verbatim from formal-conjectures `FormalConjectures/Wikipedia/Firoozbakht.lean`,
`Firoozbakht.firoozbakhtSeq` (commit `9097e2f`). `Prime` is `_root_.Prime`, as in the source.

The sequence of $\sqrt[n]{p_n}$ where $p_n$ is the n:th prime number. -/
noncomputable def firoozbakhtSeq (n : ℕ) : ℝ :=
  (n.nth Prime)^(1/(n + 1) : ℝ)

/-- The statement of formal-conjectures `FormalConjectures/Wikipedia/Firoozbakht.lean`,
`Firoozbakht.firoozbakht_conjecture` (commit `9097e2f`, `research open`), copied verbatim as a
`Prop` (its binder `(n : ℕ)` becomes `∀`).

**Firoozbakht's conjecture**: $\sqrt[n+1]{p_{n+1}} < \sqrt[n]{p_n}$ for all $n$. -/
def FiroozbakhtConjecture : Prop :=
    ∀ n : ℕ, firoozbakhtSeq (n+1) < firoozbakhtSeq n

end Firoozbakht

/-! ## The prime-gap hypothesis used here (not from formal-conjectures) -/

/-- Prime gaps are smaller than any fixed power of the prime: for every `ε > 0`,
`p_{n+1} - p_n ≤ p_n ^ ε` for all large `n`. This is the weakest natural gap hypothesis that
gives Erdős 382 (i); formal-conjectures does not state it. It follows from
`CramerConjecture.CramerConjecture` (`subpowerGaps_of_cramer`). -/
def SubpowerGaps : Prop :=
  ∀ ε > (0 : ℝ), ∀ᶠ n : ℕ in atTop, (primeGap n : ℝ) ≤ (Nat.nth Nat.Prime n : ℝ) ^ ε

/-! ## Step 1: no prime lies in `[u, v]` -/

/-- The copied `maxPrimeFac` agrees with Mathlib's `Nat.maxPrimeFac`. -/
lemma maxPrimeFac_eq_mathlib (n : ℕ) : Nat.maxPrimeFac n = _root_.Nat.maxPrimeFac n := by
  unfold Nat.maxPrimeFac _root_.Nat.maxPrimeFac
  split_ifs with h
  · subst h; simp
  · rcases n.eq_zero_or_pos with rfl | hn
    · simp [List.getLastI]
    · have hne : n.primeFactorsList ≠ [] := by
        rw [Ne, _root_.Nat.primeFactorsList_eq_nil]; omega
      rw [List.getLastI_eq_getLast?_getD, List.getLastD_eq_getLast?,
        List.getLast?_eq_getLast_of_ne_nil hne]
      rfl

namespace Erdos382

/-- If `LargestPrimeRepeated u v`, no prime `q ∈ [u, v]` has `v < 2 q`. This is the core of the
formal-conjectures proof of `lt_two_mul_of_largestPrimeRepeated`, with Bertrand's postulate
factored out. -/
lemma not_prime_of_largestPrimeRepeated {u v q : ℕ} (h : LargestPrimeRepeated u v)
    (hq : q.Prime) (huq : u ≤ q) (hqv : q ≤ v) (hvq : v < 2 * q) : False := by
  obtain ⟨hu, -, hv, hdvd⟩ := h
  rw [maxPrimeFac_eq_mathlib] at hdvd
  have hP0 : ∏ m ∈ Finset.Icc u v, m ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun m hm ↦ by have := (Finset.mem_Icc.1 hm).1; omega
  have hqP : q ∣ ∏ m ∈ Finset.Icc u v, m :=
    Finset.dvd_prod_of_mem _ (Finset.mem_Icc.2 ⟨huq, hqv⟩)
  have hP1 : 1 < ∏ m ∈ Finset.Icc u v, m :=
    lt_of_lt_of_le hq.one_lt (_root_.Nat.le_of_dvd (_root_.Nat.pos_of_ne_zero hP0) hqP)
  set p := _root_.Nat.maxPrimeFac (∏ m ∈ Finset.Icc u v, m)
  have hp : p.Prime := _root_.Nat.prime_maxPrimeFac_of_one_lt hP1
  have hpq : q ≤ p := _root_.Nat.le_maxPrimeFac hP0 hq hqP
  have hv2 : v < 2 * p := by omega
  have key : ∀ m ∈ Finset.Icc u v, p ∣ m → m = p := by
    rintro m hm ⟨k, rfl⟩
    have hm' := Finset.mem_Icc.1 hm
    rcases _root_.Nat.lt_or_ge k 2 with hk | hk
    · interval_cases k <;> omega
    · have := _root_.Nat.mul_le_mul_left p hk
      linarith [hm'.2]
  have hpmem : p ∈ Finset.Icc u v := by
    obtain ⟨m, hm, hpm⟩ := (Prime.dvd_finsetProd_iff hp.prime _).1
      (_root_.Nat.maxPrimeFac_dvd (n := ∏ m ∈ Finset.Icc u v, m))
    rwa [← key m hm hpm]
  rw [← Finset.mul_prod_erase _ _ hpmem, pow_two] at hdvd
  obtain ⟨m, hm, hpm⟩ := (Prime.dvd_finsetProd_iff hp.prime _).1
    ((mul_dvd_mul_iff_left hp.ne_zero).1 hdvd)
  exact (Finset.mem_erase.1 hm).1 (key m (Finset.mem_of_mem_erase hm) hpm)

/-- formal-conjectures `Erdos382.lt_two_mul_of_largestPrimeRepeated` (`textbook`), re-proved:
if the condition holds, then $v < 2u$. -/
theorem lt_two_mul_of_largestPrimeRepeated {u v : ℕ} (h : LargestPrimeRepeated u v) :
    v < 2 * u := by
  by_contra! hle
  have hv := h.2.2.1
  obtain ⟨q, hq, hq1, hq2⟩ := _root_.Nat.exists_prime_lt_and_le_two_mul (v / 2) (by omega)
  exact not_prime_of_largestPrimeRepeated h hq (by omega) (by omega) (by omega)

/-- If `LargestPrimeRepeated u v`, the interval `[u, v]` contains no prime. -/
theorem not_prime_of_mem_of_largestPrimeRepeated {u v q : ℕ} (h : LargestPrimeRepeated u v)
    (huq : u ≤ q) (hqv : q ≤ v) : ¬ q.Prime := fun hq ↦
  not_prime_of_largestPrimeRepeated h hq huq hqv
    (by have := lt_two_mul_of_largestPrimeRepeated h; omega)

/-- If `LargestPrimeRepeated u v`, then `[u, v]` lies strictly between consecutive primes:
there is `m` with `p_m < u`, `v < p_{m+1}`, and any prescribed lower bound `N ≤ m` holds once
`p_N < u`. -/
theorem exists_between_consecutive_primes {u v N : ℕ} (h : LargestPrimeRepeated u v)
    (hN : Nat.nth Nat.Prime N < u) :
    ∃ m, N ≤ m ∧ Nat.nth Nat.Prime m < u ∧ v < Nat.nth Nat.Prime (m + 1) := by
  have hinf := _root_.Nat.infinite_setOfPred_prime
  have hNk : N < _root_.Nat.count Nat.Prime u := (_root_.Nat.lt_nth_iff_count_lt hinf).2 hN
  obtain ⟨m, hm⟩ : ∃ m, _root_.Nat.count Nat.Prime u = m + 1 := ⟨_root_.Nat.count Nat.Prime u - 1, by omega⟩
  refine ⟨m, by omega, _root_.Nat.nth_lt_of_lt_count (by omega), ?_⟩
  have hle : u ≤ Nat.nth Nat.Prime (m + 1) := hm ▸ _root_.Nat.le_nth_count hinf u
  by_contra! hv
  exact not_prime_of_mem_of_largestPrimeRepeated h hle hv
    (_root_.Nat.prime_nth_prime (m + 1))

end Erdos382

/-! ## Step 2: the gap hypothesis implies Erdős 382 (i) -/

/-- **Sub-power prime gaps imply Erdős 382 (i).** -/
theorem erdos_382_i_of_subpowerGaps (h : SubpowerGaps) : Erdos382.Erdos382PartI := by
  intro ε hε
  obtain ⟨N, hN⟩ := eventually_atTop.1 (h ε hε)
  filter_upwards [eventually_ge_atTop (2 * Nat.nth Nat.Prime N + 2)] with v hv u huv
  have h2u := Erdos382.lt_two_mul_of_largestPrimeRepeated huv
  obtain ⟨m, hNm, hmu, hvm⟩ :=
    Erdos382.exists_between_consecutive_primes (N := N) huv (by omega)
  have huv' := huv.2.1
  have hgap : v - u < primeGap m := by unfold primeGap; omega
  have hpm_pos : (0 : ℝ) ≤ (Nat.nth Nat.Prime m : ℝ) := by positivity
  calc ((v - u : ℕ) : ℝ) ≤ (primeGap m : ℝ) := by exact_mod_cast hgap.le
    _ ≤ (Nat.nth Nat.Prime m : ℝ) ^ ε := hN m hNm
    _ ≤ (v : ℝ) ^ ε := Real.rpow_le_rpow hpm_pos (by exact_mod_cast (by omega : _ ≤ v)) hε.le

/-! ## Step 3: Cramér, its strict form and Firoozbakht each imply `SubpowerGaps` -/

lemma tendsto_nth_prime_real :
    Tendsto (fun n : ℕ => (Nat.nth Nat.Prime n : ℝ)) atTop atTop :=
  tendsto_natCast_atTop_atTop.comp
    (_root_.Nat.nth_strictMono _root_.Nat.infinite_setOfPred_prime).tendsto_atTop

/-- **Cramér's conjecture implies sub-power prime gaps**, since `(log x)^2 = o(x^ε)`. -/
theorem subpowerGaps_of_cramer (h : CramerConjecture.CramerConjecture) : SubpowerGaps := by
  intro ε hε
  have hlog : (fun x : ℝ => Real.log x ^ 2) =o[atTop] fun x => x ^ ε := by
    simpa using isLittleO_log_rpow_rpow_atTop (2 : ℝ) hε
  have ho := h.trans_isLittleO (hlog.comp_tendsto tendsto_nth_prime_real)
  filter_upwards [ho.bound one_pos] with n hn
  have hp : (0 : ℝ) ≤ (Nat.nth Nat.Prime n : ℝ) := by positivity
  simpa [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hp ε)] using hn

/-- **The strict numerical Cramér inequality implies Cramér's conjecture.** -/
theorem cramer_of_strictBound (h : CramerConjecture.StrictBound) :
    CramerConjecture.CramerConjecture := by
  refine Asymptotics.IsBigO.of_bound 1 ?_
  filter_upwards [eventually_ge_atTop 4] with n hn
  have hp : (2 : ℝ) ≤ (Nat.nth Nat.Prime n : ℝ) := by
    exact_mod_cast (_root_.Nat.prime_nth_prime n).two_le
  have hlog : 0 < Real.log (Nat.nth Nat.Prime n) := Real.log_pos (by linarith)
  have hr := h n hn
  rw [CramerConjecture.cramerRatio, div_lt_one (by positivity)] at hr
  simp only [Real.norm_eq_abs, one_mul, Nat.abs_cast, abs_pow, abs_of_pos hlog]
  exact hr.le

/-- `π(p_k) = k + 1`, written with Mathlib's `Nat.primeCounting`. -/
lemma primeCounting_nth (k : ℕ) : _root_.Nat.primeCounting (Nat.nth Nat.Prime k) = k + 1 :=
  _root_.Nat.count_nth_succ_of_infinite _root_.Nat.infinite_setOfPred_prime k

/-- Chebyshev's lower bound at a prime: `p_k log 2 ≤ (k + 1) log p_k` once `p_k ≥ 7`. -/
lemma nth_mul_log_two_le {k : ℕ} (hk : 7 ≤ Nat.nth Nat.Prime k) :
    (Nat.nth Nat.Prime k : ℝ) * Real.log 2 ≤ (k + 1 : ℝ) * Real.log (Nat.nth Nat.Prime k) := by
  have h1 := Chebyshev.psi_ge_of_seven_le hk
  have h2 := Chebyshev.psi_le_primeCounting_mul_log (Nat.nth Nat.Prime k)
  rw [primeCounting_nth] at h2
  push_cast at h2
  linarith

/-- **Firoozbakht's conjecture implies Cramér's conjecture**, with the explicit bound
`p_{k+1} - p_k ≤ (2 / log 2) (log p_k)^2` for large `k`. Firoozbakht gives
`p_{k+1} < p_k · exp(log p_k / (k + 1))`, and Chebyshev's `π(x) log x ≥ x log 2` gives
`log p_k / (k + 1) ≤ (log p_k)^2 / (p_k log 2)`, which is at most `1` for large `k`; then
`exp t - 1 ≤ 2 t` on `[0, 1]`. -/
theorem cramer_of_firoozbakht (h : Firoozbakht.FiroozbakhtConjecture) :
    CramerConjecture.CramerConjecture := by
  have hPrime : (fun n : ℕ => Prime n) = Nat.Prime := funext fun n ↦ propext _root_.Nat.prime_iff.symm
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  -- `(log x)^2 ≤ (log 2) x` for large `x`
  have hsmall : ∀ᶠ k : ℕ in atTop, Real.log (Nat.nth Nat.Prime k) ^ 2 ≤
      Real.log 2 * (Nat.nth Nat.Prime k : ℝ) := by
    have hlo : (fun x : ℝ => Real.log x ^ 2) =o[atTop] fun x => x := by
      simpa using isLittleO_log_rpow_rpow_atTop (2 : ℝ) one_pos
    filter_upwards [(hlo.comp_tendsto tendsto_nth_prime_real).bound hlog2,
      tendsto_nth_prime_real.eventually_ge_atTop 0] with k hk hk0
    simpa [Real.norm_eq_abs, abs_of_nonneg hk0] using hk
  have h7 : ∀ᶠ k : ℕ in atTop, 7 ≤ Nat.nth Nat.Prime k := by
    filter_upwards [eventually_ge_atTop 5] with k hk
    have := _root_.Nat.add_two_le_nth_prime k
    omega
  refine Asymptotics.IsBigO.of_bound (2 / Real.log 2) ?_
  filter_upwards [hsmall, h7] with k hsk h7k
  set a : ℝ := (Nat.nth Nat.Prime k : ℝ) with ha
  set b : ℝ := (Nat.nth Nat.Prime (k + 1) : ℝ) with hb
  have ha7 : (7 : ℝ) ≤ a := by rw [ha]; exact_mod_cast h7k
  have ha0 : 0 < a := by linarith
  have hb0 : 0 < b := by
    have := (_root_.Nat.prime_nth_prime (k + 1)).pos
    rw [hb]; exact_mod_cast this
  have habN : Nat.nth Nat.Prime k < Nat.nth Nat.Prime (k + 1) :=
    _root_.Nat.nth_strictMono _root_.Nat.infinite_setOfPred_prime (by omega)
  have hla : 0 < Real.log a := Real.log_pos (by linarith)
  -- Firoozbakht at `k`, in logarithms
  have hF := h k
  simp only [Firoozbakht.firoozbakhtSeq, hPrime] at hF
  rw [← ha, ← hb] at hF
  have hF' := Real.log_lt_log (Real.rpow_pos_of_pos hb0 _) hF
  rw [Real.log_rpow hb0, Real.log_rpow ha0] at hF'
  push_cast at hF'
  set L := Real.log a with hL
  set t : ℝ := L / (k + 1 : ℝ) with ht
  have hk1 : (0 : ℝ) < k + 1 := by positivity
  have hlogb : Real.log b < L + t := by
    have e1 : Real.log b = (k + 1 + 1) * (1 / ((k : ℝ) + 1 + 1) * Real.log b) := by
      field_simp
    have e2 : L + t = (k + 1 + 1) * (1 / ((k : ℝ) + 1) * L) := by
      rw [ht]; field_simp
    rw [e1, e2]
    exact mul_lt_mul_of_pos_left hF' (by positivity)
  have hbexp : b < a * Real.exp t := by
    have := Real.exp_lt_exp.2 hlogb
    rwa [Real.exp_log hb0, Real.exp_add, hL, Real.exp_log ha0] at this
  have ht0 : 0 ≤ t := by positivity
  have hcheb := nth_mul_log_two_le h7k
  rw [← ha, ← hL] at hcheb
  have htL : t ≤ L ^ 2 / (a * Real.log 2) := by
    rw [ht, div_le_div_iff₀ hk1 (by positivity)]
    nlinarith
  have ht1 : t ≤ 1 := htL.trans ((div_le_one (by positivity)).2 (by linarith))
  have hexp : Real.exp t - 1 ≤ 2 * t := by
    have := Real.abs_exp_sub_one_le (x := t) (by rw [abs_of_nonneg ht0]; exact ht1)
    rw [abs_of_nonneg ht0] at this
    exact (le_abs_self _).trans this
  have hgap : (primeGap k : ℝ) = b - a := by
    rw [primeGap, Nat.cast_sub habN.le, hb, ha]
  have hmain : (primeGap k : ℝ) ≤ 2 / Real.log 2 * L ^ 2 := by
    rw [hgap]
    have h1 : b - a ≤ a * (2 * t) := by nlinarith
    have h2 : a * (2 * t) ≤ 2 / Real.log 2 * L ^ 2 := by
      have : a * t ≤ L ^ 2 / Real.log 2 := by
        calc a * t ≤ a * (L ^ 2 / (a * Real.log 2)) := mul_le_mul_of_nonneg_left htL ha0.le
          _ = L ^ 2 / Real.log 2 := by field_simp
      calc a * (2 * t) = 2 * (a * t) := by ring
        _ ≤ 2 * (L ^ 2 / Real.log 2) := by linarith
        _ = 2 / Real.log 2 * L ^ 2 := by ring
    linarith
  have hpg : (0 : ℝ) ≤ primeGap k := by positivity
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hpg, abs_of_nonneg (sq_nonneg _)]
  exact hmain

/-! ## Headline theorems -/

/-- **Cramér's conjecture implies Erdős 382 (i)** (Cambie's observation). -/
theorem erdos_382_i_of_cramer (h : CramerConjecture.CramerConjecture) :
    Erdos382.Erdos382PartI :=
  erdos_382_i_of_subpowerGaps (subpowerGaps_of_cramer h)

/-- **The strict numerical Cramér inequality implies Erdős 382 (i).** -/
theorem erdos_382_i_of_strictBound (h : CramerConjecture.StrictBound) :
    Erdos382.Erdos382PartI :=
  erdos_382_i_of_cramer (cramer_of_strictBound h)

/-- **Firoozbakht's conjecture implies Erdős 382 (i).** -/
theorem erdos_382_i_of_firoozbakht (h : Firoozbakht.FiroozbakhtConjecture) :
    Erdos382.Erdos382PartI :=
  erdos_382_i_of_cramer (cramer_of_firoozbakht h)

end Implications.PrimeGaps
