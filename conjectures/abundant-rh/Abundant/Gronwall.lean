import Abundant.SolePlanat

/-!
# Gronwall's lower bound along multiples, from Nicolas' inequality

For every `N ≥ 1` and every `c < e^γ` there are multiples `m = a N`, as large as we like, with
`f(m) = σ(m)/(m log log m) > c`. This is the half `limsup f ≥ e^γ` of Gronwall's theorem,
sharpened to run through multiples of a fixed `N` (Caveney–Nicolas–Sondow's Lemma 1 has the same
shape). The proof uses Nicolas' inequality `N_k/φ(N_k) > e^γ log log N_k` (an explicit
hypothesis here) instead of Mertens' third theorem, which is not in Mathlib.

Take `m = N · N_k^e`. Then
* `σ(m)/m ≥ σ(N_k^e)/N_k^e = (N_k/φ(N_k)) ∏_{p ≤ p_k}(1 − p^{−(e+1)}) ≥ (N_k/φ(N_k))/Z_e`,
  with `Z_e = 1 + 8/2^{e+1} ≥ ζ(e+1)` (Euler product, `prod_inv_one_sub_invPow_le`);
* `log log m ≤ log(e+1) + log log N_k` once `N ≤ N_k`.
So `f(m) > e^γ L/(Z_e (log(e+1) + L))`, `L = log log N_k`; choose `e`, then `k`.
-/

namespace Abundant

open Real Finset ArithmeticFunction
open scoped ArithmeticFunction.sigma

/-! ### `n ↦ n^{-t}` and its Euler product -/

/-- The completely multiplicative function `n ↦ n^{-t}`. -/
noncomputable def invPow (t : ℕ) : ℕ →* ℝ where
  toFun n := ((n : ℝ) ^ t)⁻¹
  map_one' := by simp
  map_mul' m n := by push_cast; rw [mul_pow, mul_inv]

lemma invPow_apply (t n : ℕ) : invPow t n = ((n : ℝ) ^ t)⁻¹ := rfl

lemma invPow_nonneg (t n : ℕ) : 0 ≤ invPow t n := by
  rw [invPow_apply]; positivity

/-- `n^{-t} ≤ [n = 1] + (4/2^t) n^{-2}` for `t ≥ 2`. -/
lemma invPow_le_dom {t : ℕ} (ht : 2 ≤ t) (n : ℕ) :
    invPow t n ≤ (if n = 1 then 1 else 0) + (4 / 2 ^ t) * (1 / (n : ℝ) ^ 2) := by
  rcases Nat.lt_or_ge n 2 with h | h
  · interval_cases n
    · simp [invPow_apply, zero_pow (show t ≠ 0 by omega)]
    · simp only [invPow_apply, Nat.cast_one, one_pow, inv_one, ite_true]
      have : (0 : ℝ) ≤ 4 / 2 ^ t * (1 / 1 ^ 2) := by positivity
      linarith
  · have hn1 : n ≠ 1 := by omega
    simp only [hn1, ite_false, zero_add, invPow_apply]
    have hn : (2 : ℝ) ≤ n := by exact_mod_cast h
    obtain ⟨s, rfl⟩ : ∃ s, t = s + 2 := ⟨t - 2, by omega⟩
    have h4 : (4 : ℝ) / 2 ^ (s + 2) * (1 / (n : ℝ) ^ 2) = ((2 : ℝ) ^ s * (n : ℝ) ^ 2)⁻¹ := by
      rw [pow_add]; field_simp; norm_num
    rw [h4, pow_add]
    apply inv_anti₀ (by positivity)
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by norm_num) hn s) (by positivity)

lemma hasSum_dom (t : ℕ) :
    HasSum (fun n : ℕ ↦ (if n = 1 then (1 : ℝ) else 0) + (4 / 2 ^ t) * (1 / (n : ℝ) ^ 2))
      (1 + (4 / 2 ^ t) * (π ^ 2 / 6)) :=
  (hasSum_ite_eq 1 (1 : ℝ)).add (hasSum_zeta_two.mul_left _)

lemma summable_invPow {t : ℕ} (ht : 2 ≤ t) : Summable (fun n : ℕ ↦ invPow t n) :=
  Summable.of_nonneg_of_le (invPow_nonneg t) (invPow_le_dom ht) (hasSum_dom t).summable

/-- `ζ(t) ≤ 1 + 8/2^t` for `t ≥ 2`. -/
lemma tsum_invPow_le {t : ℕ} (ht : 2 ≤ t) : ∑' n : ℕ, invPow t n ≤ 1 + 8 / 2 ^ t := by
  have h := hasSum_le (invPow_le_dom ht) (summable_invPow ht).hasSum (hasSum_dom t)
  have hpi : π ^ 2 / 6 < 2 := by
    have := Real.pi_lt_d2
    have h0 := Real.pi_pos
    nlinarith
  have : (4 / 2 ^ t : ℝ) * (π ^ 2 / 6) ≤ 8 / 2 ^ t := by
    have h2 : (0 : ℝ) < 2 ^ t := by positivity
    rw [div_mul_eq_mul_div, div_le_div_iff_of_pos_right h2]
    linarith
  linarith

lemma one_sub_invPow_pos {t : ℕ} (ht : 1 ≤ t) {p : ℕ} (hp : p.Prime) : 0 < 1 - invPow t p := by
  rw [invPow_apply, sub_pos]
  have h2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have : (1 : ℝ) < (p : ℝ) ^ t := one_lt_pow₀ (by linarith) (by omega)
  exact inv_lt_one_of_one_lt₀ this

/-- Finite Euler product: `∏_{p ∈ s} (1 − p^{−t}) ≥ 1/(1 + 8/2^t)` for a set of primes `s`. -/
lemma inv_le_prod_one_sub_invPow {t : ℕ} (ht : 2 ≤ t) (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime) :
    (1 + 8 / 2 ^ t : ℝ)⁻¹ ≤ ∏ p ∈ s, (1 - invPow t p) := by
  have hfilt : s.filter Nat.Prime = s := Finset.filter_true_of_mem hs
  have h := EulerProduct.prod_filter_prime_geometric_eq_tsum_factoredNumbers (summable_invPow ht) s
  rw [hfilt, Finset.prod_inv_distrib] at h
  have hle : ∑' m : Nat.factoredNumbers s, invPow t m ≤ ∑' n : ℕ, invPow t n :=
    (summable_invPow ht).tsum_subtype_le (fun n ↦ invPow t n) _ (invPow_nonneg t)
  have hP : 0 < ∏ p ∈ s, (1 - invPow t p) :=
    Finset.prod_pos fun p hp ↦ one_sub_invPow_pos (by omega) (hs p hp)
  exact inv_le_of_inv_le₀ hP (h ▸ hle.trans (tsum_invPow_le ht))

/-! ### `σ(n)/n` -/

lemma sigma_div_eq {n : ℕ} (hn : n ≠ 0) :
    (σ 1 n : ℝ) / n = ∑ d ∈ n.divisors, 1 / (d : ℝ) := by
  have h1 : (σ 1 n : ℝ) = ∑ d ∈ n.divisors, ((n / d : ℕ) : ℝ) := by
    rw [sigma_one_apply, ← Nat.sum_div_divisors n (fun d ↦ d)]
    push_cast; rfl
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  rw [h1, Finset.sum_div]
  refine Finset.sum_congr rfl fun d hd ↦ ?_
  have hdn : d ∣ n := Nat.dvd_of_mem_divisors hd
  have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast (Nat.pos_of_mem_divisors hd).ne'
  rw [Nat.cast_div hdn hd0]
  field_simp

/-- `σ(a)/a ≤ σ(b)/b` when `a ∣ b`. -/
lemma sigma_div_le_of_dvd {a b : ℕ} (hb : b ≠ 0) (h : a ∣ b) :
    (σ 1 a : ℝ) / a ≤ (σ 1 b : ℝ) / b := by
  have ha : a ≠ 0 := by rintro rfl; exact hb (zero_dvd_iff.mp h)
  rw [sigma_div_eq ha, sigma_div_eq hb]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Nat.divisors_subset_of_dvd hb h)
    (fun d _ _ ↦ by positivity)

/-- `σ(p^e)/p^e = (p/(p−1))(1 − p^{−(e+1)})`. -/
lemma sigma_prime_pow_div {p : ℕ} (hp : p.Prime) (e : ℕ) :
    (σ 1 (p ^ e) : ℝ) / ((p ^ e : ℕ) : ℝ) = (p : ℝ) / (p - 1) * (1 - invPow (e + 1) p) := by
  rw [sigma_one_apply_prime_pow hp, invPow_apply]
  push_cast
  have h2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hp1 : (p : ℝ) ≠ 1 := by linarith
  have hp0 : (p : ℝ) ≠ 0 := by linarith
  have hpm : (p : ℝ) - 1 ≠ 0 := sub_ne_zero.mpr hp1
  rw [geom_sum_eq hp1]
  field_simp
  ring

/-- For a set of primes `s`, `σ(∏ p^e)/∏ p^e = (∏ p/(p−1)) ∏ (1 − p^{−(e+1)})`. -/
lemma sigma_prod_pow_div (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime) (e : ℕ) :
    (σ 1 (∏ p ∈ s, p ^ e) : ℝ) / ((∏ p ∈ s, p ^ e : ℕ) : ℝ)
      = (∏ p ∈ s, (p : ℝ) / (p - 1)) * ∏ p ∈ s, (1 - invPow (e + 1) p) := by
  have hcop : (s : Set ℕ).Pairwise (Function.onFun Nat.Coprime fun p ↦ p ^ e) := by
    intro p hp q hq hpq
    exact Nat.Coprime.pow _ _ ((Nat.coprime_primes (hs p hp) (hs q hq)).mpr hpq)
  rw [IsMultiplicative.map_prod (fun p ↦ p ^ e) isMultiplicative_sigma s hcop]
  push_cast
  rw [← Finset.prod_mul_distrib, ← Finset.prod_div_distrib]
  refine Finset.prod_congr rfl fun p hp ↦ ?_
  have := sigma_prime_pow_div (hs p hp) e
  push_cast at this
  exact this

/-- `N/φ(N) = ∏_{p ∈ s} p/(p−1)` for `N = ∏_{p ∈ s} p`, `s` a set of primes. -/
lemma prod_div_totient (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime) :
    ((∏ p ∈ s, p : ℕ) : ℝ) / (Nat.totient (∏ p ∈ s, p) : ℝ) = ∏ p ∈ s, (p : ℝ) / (p - 1) := by
  have hφ := totient_eq_mul_prod_real (∏ p ∈ s, p)
  rw [Nat.primeFactors_prod hs] at hφ
  have hN : ((∏ p ∈ s, p : ℕ) : ℝ) ≠ 0 := by
    have : 0 < ∏ p ∈ s, p := Finset.prod_pos fun p hp ↦ (hs p hp).pos
    exact_mod_cast this.ne'
  rw [hφ, div_mul_cancel_left₀ hN, ← Finset.prod_inv_distrib]
  refine Finset.prod_congr rfl fun p hp ↦ ?_
  have h2 : (2 : ℝ) ≤ p := by exact_mod_cast (hs p hp).two_le
  have hp0 : (p : ℝ) ≠ 0 := by linarith
  have hpm : (p : ℝ) - 1 ≠ 0 := by linarith
  field_simp

/-! ### Primorials -/

/-- The primes `p_1, …, p_k` of `N_k`. -/
noncomputable def primesOf (k : ℕ) : Finset ℕ := (Finset.range k).image (Nat.nth Nat.Prime)

lemma primesOf_prime {k p : ℕ} (hp : p ∈ primesOf k) : p.Prime := by
  obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hp
  exact Nat.prime_nth_prime i

lemma kthPrimorial_eq_prod (k : ℕ) : Nicolas.kthPrimorial k = ∏ p ∈ primesOf k, p := by
  rw [primesOf, Finset.prod_image]
  · rfl
  · intro i _ j _ h
    exact Nat.nth_injective Nat.infinite_setOf_prime h

/-- `σ(N_k^e)/N_k^e = (N_k/φ(N_k)) ∏_{p ≤ p_k}(1 − p^{−(e+1)})`. -/
lemma sigma_kthPrimorial_pow_div (k e : ℕ) :
    (σ 1 (Nicolas.kthPrimorial k ^ e) : ℝ) / ((Nicolas.kthPrimorial k ^ e : ℕ) : ℝ)
      = ((Nicolas.kthPrimorial k : ℕ) : ℝ) / (Nat.totient (Nicolas.kthPrimorial k) : ℝ)
        * ∏ p ∈ primesOf k, (1 - invPow (e + 1) p) := by
  rw [kthPrimorial_eq_prod, ← Finset.prod_pow, sigma_prod_pow_div _ (fun p hp ↦ primesOf_prime hp),
    prod_div_totient _ (fun p hp ↦ primesOf_prime hp)]

/-! ### The lower bound -/

/-- **Gronwall's lower bound along multiples**, from Nicolas' inequality: for every `N ≥ 1`,
every `c < e^γ` and every `B`, some multiple `m = a N ≥ B` has `σ(m)/(m log log m) > c`. -/
theorem exists_mul_robinRatio_gt (hNic : Nicolas.NicolasStatement) {N : ℕ} (hN : 1 ≤ N)
    {c : ℝ} (hc : c < Real.exp Real.eulerMascheroniConstant) (B : ℕ) :
    ∃ a : ℕ, 1 ≤ a ∧ B ≤ a * N ∧ c < robinRatio (a * N) := by
  set g := Real.exp Real.eulerMascheroniConstant with hg_def
  have hg : 0 < g := Real.exp_pos _
  -- Step 1: the exponent `e`, with `c · Z_e < e^γ`.
  obtain ⟨e, he1, hZ⟩ : ∃ e : ℕ, 1 ≤ e ∧ c * (1 + 8 / 2 ^ (e + 1)) < g := by
    rcases le_or_gt c 0 with hc0 | hc0
    · refine ⟨1, le_rfl, ?_⟩
      have : c * (1 + 8 / 2 ^ (1 + 1)) ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg hc0 (by positivity)
      linarith
    · have hη : 0 < g / c - 1 := by rw [sub_pos, one_lt_div hc0]; exact hc
      obtain ⟨e, he⟩ := pow_unbounded_of_one_lt (8 / (g / c - 1)) (by norm_num : (1 : ℝ) < 2)
      refine ⟨e + 1, by omega, ?_⟩
      have h2 : (2 : ℝ) ^ e ≤ 2 ^ (e + 1 + 1) := pow_le_pow_right₀ (by norm_num) (by omega)
      have h3 : 8 / (2 : ℝ) ^ (e + 1 + 1) < g / c - 1 := by
        rw [div_lt_iff₀ (by positivity)]
        rw [div_lt_iff₀ hη] at he
        nlinarith
      have : 1 + 8 / (2 : ℝ) ^ (e + 1 + 1) < g / c := by linarith
      calc c * (1 + 8 / 2 ^ (e + 1 + 1)) < c * (g / c) := mul_lt_mul_of_pos_left this hc0
        _ = g := by field_simp
  set Z : ℝ := 1 + 8 / 2 ^ (e + 1) with hZdef
  have hZpos : 0 < Z := by positivity
  set r : ℝ := c * Z with hr
  set D : ℝ := Real.log ((e : ℝ) + 1) with hD_def
  have hD : 0 ≤ D := Real.log_nonneg (by have : (0 : ℝ) ≤ e := Nat.cast_nonneg e; linarith)
  have hgr : 0 < g - r := by linarith
  -- Step 2: the index `k`, with `log log N_k > X`.
  set X : ℝ := |r| * D / (g - r) + 1 with hX
  have hX0 : 0 ≤ |r| * D / (g - r) := by positivity
  obtain ⟨k, hk, hkX⟩ : ∃ k : ℕ, max (max N B) 3 ≤ k ∧ 2 * Real.exp X < k := by
    obtain ⟨k0, hk0⟩ := exists_nat_gt (2 * Real.exp X)
    refine ⟨max (max (max N B) 3) k0, le_max_left _ _, lt_of_lt_of_le hk0 ?_⟩
    exact_mod_cast le_max_right _ _
  have hkN : N ≤ k := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hk
  have hkB : B ≤ k := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hk
  have hk3 : 3 ≤ k := le_trans (le_max_right _ _) hk
  set Nk := Nicolas.kthPrimorial k with hNk_def
  have hNk2 : 2 ^ k ≤ Nk := two_pow_le_kthPrimorial k
  have hkpow : k < 2 ^ k := Nat.lt_two_pow_self
  have hNkpos : 0 < Nk := lt_of_lt_of_le (by positivity) hNk2
  have hlogNk : Real.exp X < Real.log Nk := by
    have h1 : (k : ℝ) * Real.log 2 ≤ Real.log Nk := by
      rw [← Real.log_pow]
      apply Real.log_le_log (by positivity)
      exact_mod_cast hNk2
    have := Real.log_two_gt_d9
    have hk0 : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
    nlinarith
  set L := Real.log (Real.log Nk) with hL_def
  have hL : X < L := by
    rw [show X = Real.log (Real.exp X) from (Real.log_exp X).symm]
    exact Real.log_lt_log (Real.exp_pos X) hlogNk
  have hLpos : 0 < L := by linarith
  -- Step 3: the multiple `m = N_k^e · N`.
  set a := Nk ^ e with ha_def
  have ha1 : 1 ≤ a := Nat.one_le_pow _ _ hNkpos
  have hNka : Nk ≤ a := Nat.le_self_pow (by omega) Nk
  have ham : a ≤ a * N := Nat.le_mul_of_pos_right a hN
  refine ⟨a, ha1, by omega, ?_⟩
  set m := a * N with hm_def
  have hm0 : m ≠ 0 := by positivity
  have hmpos : (0 : ℝ) < m := by exact_mod_cast Nat.pos_of_ne_zero hm0
  -- `σ(m)/m ≥ (N_k/φ(N_k)) / Z`
  have hsig : (σ 1 a : ℝ) / a ≤ (σ 1 m : ℝ) / m := sigma_div_le_of_dvd hm0 (dvd_mul_right a N)
  have ha_eq := sigma_kthPrimorial_pow_div k e
  rw [← hNk_def, ← ha_def] at ha_eq
  have hP := inv_le_prod_one_sub_invPow (show 2 ≤ e + 1 by omega) (primesOf k)
    (fun p hp ↦ primesOf_prime hp)
  have hNic' : g * L < (Nk : ℝ) / (Nat.totient Nk : ℝ) := hNic k (by omega)
  have hφpos : (0 : ℝ) < (Nk : ℝ) / (Nat.totient Nk : ℝ) := lt_trans (by positivity) hNic'
  have hσm : g * L / Z ≤ (σ 1 m : ℝ) / m := by
    calc g * L / Z = g * L * Z⁻¹ := div_eq_mul_inv _ _
      _ ≤ (Nk : ℝ) / (Nat.totient Nk : ℝ) * Z⁻¹ :=
          mul_le_mul_of_nonneg_right hNic'.le (by positivity)
      _ ≤ (Nk : ℝ) / (Nat.totient Nk : ℝ) * ∏ p ∈ primesOf k, (1 - invPow (e + 1) p) :=
          mul_le_mul_of_nonneg_left hP hφpos.le
      _ = (σ 1 a : ℝ) / a := by rw [ha_eq]
      _ ≤ (σ 1 m : ℝ) / m := hsig
  -- `0 < log log m ≤ log(e+1) + log log N_k`
  have hNkm : (Nk : ℝ) ≤ m := by exact_mod_cast (show Nk ≤ m by omega)
  have hNkpos' : (0 : ℝ) < Nk := by exact_mod_cast hNkpos
  have hlogNk_le : Real.log Nk ≤ Real.log m := Real.log_le_log hNkpos' hNkm
  have hexpX : 1 < Real.exp X := by
    rw [← Real.exp_zero]; exact Real.exp_lt_exp.mpr (by linarith)
  have hlogNk_pos : 0 < Real.log Nk := by linarith
  have hlogm : Real.log m ≤ ((e : ℝ) + 1) * Real.log Nk := by
    have hNle : (N : ℝ) ≤ Nk := by exact_mod_cast (show N ≤ Nk by omega)
    have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
    rw [hm_def, ha_def]
    push_cast
    rw [Real.log_mul (by positivity) hNpos.ne', Real.log_pow]
    have := Real.log_le_log hNpos hNle
    linarith
  have hLLm_pos : 0 < Real.log (Real.log m) := Real.log_pos (by linarith)
  have hLLm : Real.log (Real.log m) ≤ D + L := by
    calc Real.log (Real.log m) ≤ Real.log (((e : ℝ) + 1) * Real.log Nk) :=
          Real.log_le_log (by linarith) hlogm
      _ = D + L := by
          rw [Real.log_mul (by positivity) hlogNk_pos.ne']
  -- conclude
  have hratio : robinRatio m = (σ 1 m : ℝ) / m / Real.log (Real.log m) := by
    rw [robinRatio, div_div]
  rw [hratio]
  have hfinal : c < g * L / Z / (D + L) := by
    rw [lt_div_iff₀ (by linarith), lt_div_iff₀ hZpos]
    have h1 : |r| * D < (g - r) * L := by
      have : |r| * D / (g - r) < L := by linarith
      rwa [div_lt_iff₀ hgr, mul_comm L] at this
    have h2 : r * D ≤ |r| * D := mul_le_mul_of_nonneg_right (le_abs_self r) hD
    have : c * (D + L) * Z = r * (D + L) := by rw [hr]; ring
    rw [this]
    nlinarith
  calc c < g * L / Z / (D + L) := hfinal
    _ ≤ (σ 1 m : ℝ) / m / (D + L) := div_le_div_of_nonneg_right hσm (by linarith)
    _ ≤ (σ 1 m : ℝ) / m / Real.log (Real.log m) :=
        div_le_div_of_nonneg_left (by positivity) hLLm_pos hLLm

end Abundant
