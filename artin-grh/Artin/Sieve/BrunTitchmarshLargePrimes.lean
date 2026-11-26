import Artin.Sieve.BrunTitchmarsh
import Mathlib.NumberTheory.Chebyshev
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Large primes `√x / log² x < q ≤ √x log x` (blueprint B3)

Let `ξ₂ = √x / log² x` and `ξ₃ = √x · log x`. Brun–Titchmarsh (`primeCountAP_le`) gives, for a
prime `q ≤ ξ₃`, `π(x; q, 1) ≪ x / (q log(x/q)) ≪ x / (q log x)`, because `x/q ≥ √x / log x`.
Chebyshev's bound `θ(y) ≤ y log 4`, over dyadic blocks, gives
`∑_{ξ₂ < q ≤ ξ₃} 1/q ≪ log(ξ₃/ξ₂) / log ξ₂ ≪ log log x / log x`. Together:

* `largePrimesSum_le`: `∑_{ξ₂ < q ≤ ξ₃, q prime} π(x; q, 1) ≤ 23040000 · x log log x / log² x`
  for `x ≥ e^256`;
* `largePrimesSum_isLittleO`: this sum is `o(π(x))`;
* `largePrimeCount_le`, `largePrimeCount_isLittleO`: the same bounds for the number of primes
  `p < x`, `p ∤ a`, sifted out in Hooley's sense by some prime `q ∈ (ξ₂, ξ₃]`.

Unconditional. The constants and `x₀ = e^256` are far from optimal.
-/

namespace Artin

open Finset Real Filter Asymptotics
open Artin.BrunTitchmarsh

/-- `ξ₂ = √x / log² x`. -/
noncomputable def xi2 (x : ℝ) : ℝ := Real.sqrt x / Real.log x ^ 2

/-- `ξ₃ = √x · log x`. -/
noncomputable def xi3 (x : ℝ) : ℝ := Real.sqrt x * Real.log x

/-- The primes `q` with `ξ₂ < q ≤ ξ₃`. -/
noncomputable def largePrimes (x : ℝ) : Finset ℕ :=
  (Ioc ⌊xi2 x⌋₊ ⌊xi3 x⌋₊).filter Nat.Prime

/-- `∑_{ξ₂ < q ≤ ξ₃, q prime} #{p ≤ x prime : p ≡ 1 (mod q)}`. -/
noncomputable def largePrimesSum (x : ℝ) : ℕ :=
  ∑ q ∈ largePrimes x, primeCountAP q x

/-! ### Prime reciprocals over dyadic blocks -/

/-- `∑_{B < q ≤ 2B, q prime} 1/q ≤ 2 log 4 / log B` for `B ≥ 2` (Chebyshev). -/
lemma sum_inv_primes_dyadic_le {B : ℝ} (hB : 2 ≤ B) :
    ∑ q ∈ (Ioc ⌊B⌋₊ ⌊2 * B⌋₊).filter Nat.Prime, (q : ℝ)⁻¹ ≤ 2 * Real.log 4 / Real.log B := by
  have hB0 : 0 < B := by linarith
  have hlogB : 0 < Real.log B := Real.log_pos (by linarith)
  set Q := (Ioc ⌊B⌋₊ ⌊2 * B⌋₊).filter Nat.Prime with hQ
  have hgt : ∀ q ∈ Q, B < q := fun q hq => by
    simp only [hQ, mem_filter, mem_Ioc] at hq
    exact (Nat.floor_lt hB0.le).mp hq.1.1
  -- `#Q · log B ≤ θ(2B) ≤ 2B log 4`
  have hcard : (Q.card : ℝ) * Real.log B ≤ 2 * B * Real.log 4 := by
    have hθ : ∑ q ∈ Q, Real.log q ≤ Chebyshev.theta (2 * B) := by
      rw [Chebyshev.theta]
      apply sum_le_sum_of_subset_of_nonneg
      · intro q hq
        simp only [hQ, mem_filter, mem_Ioc] at hq ⊢
        exact ⟨⟨by omega, hq.1.2⟩, hq.2⟩
      · intro q _ _
        exact Real.log_natCast_nonneg q
    have hle : (Q.card : ℝ) * Real.log B ≤ ∑ q ∈ Q, Real.log q := by
      rw [← nsmul_eq_mul, ← sum_const]
      exact sum_le_sum fun q hq => Real.log_le_log hB0 (hgt q hq).le
    have := Chebyshev.theta_le_log4_mul_x (x := 2 * B) (by linarith)
    linarith
  calc ∑ q ∈ Q, (q : ℝ)⁻¹ ≤ ∑ _q ∈ Q, B⁻¹ :=
        sum_le_sum fun q hq => inv_anti₀ hB0 (hgt q hq).le
    _ = Q.card * B⁻¹ := by rw [sum_const, nsmul_eq_mul]
    _ ≤ 2 * Real.log 4 / Real.log B := by
        rw [le_div_iff₀ hlogB]
        calc (Q.card : ℝ) * B⁻¹ * Real.log B = (Q.card * Real.log B) * B⁻¹ := by ring
          _ ≤ (2 * B * Real.log 4) * B⁻¹ := by gcongr
          _ = 2 * Real.log 4 := by field_simp

/-- `∑_{A < q ≤ 2^J A, q prime} 1/q ≤ J · 2 log 4 / log A` for `A ≥ 2`. -/
lemma sum_inv_primes_le {A : ℝ} (hA : 2 ≤ A) (J : ℕ) :
    ∑ q ∈ (Ioc ⌊A⌋₊ ⌊A * 2 ^ J⌋₊).filter Nat.Prime, (q : ℝ)⁻¹ ≤
      J * (2 * Real.log 4 / Real.log A) := by
  have hlogA : 0 < Real.log A := Real.log_pos (by linarith)
  induction J with
  | zero => simp
  | succ J ih =>
    have hAJ : A ≤ A * 2 ^ J := le_mul_of_one_le_right (by linarith) (one_le_pow₀ (by norm_num))
    have hmono1 : ⌊A⌋₊ ≤ ⌊A * 2 ^ J⌋₊ := Nat.floor_mono hAJ
    have hmono2 : ⌊A * 2 ^ J⌋₊ ≤ ⌊A * 2 ^ (J + 1)⌋₊ := Nat.floor_mono (by
      rw [pow_succ]; nlinarith [pow_pos (show (0:ℝ) < 2 by norm_num) J])
    rw [sum_filter, ← sum_Ioc_consecutive _ hmono1 hmono2, ← sum_filter, ← sum_filter]
    have hblock := sum_inv_primes_dyadic_le (B := A * 2 ^ J) (by linarith)
    have h2 : 2 * (A * 2 ^ J) = A * 2 ^ (J + 1) := by ring
    rw [h2] at hblock
    have hlog : 2 * Real.log 4 / Real.log (A * 2 ^ J) ≤ 2 * Real.log 4 / Real.log A := by
      have h4 : 0 ≤ 2 * Real.log 4 := by positivity
      exact div_le_div_of_nonneg_left h4 hlogA (Real.log_le_log (by linarith) hAJ)
    push_cast
    linarith

/-! ### Elementary estimates for `x ≥ e^256` -/

section Estimates

variable {x : ℝ} (hx : Real.exp 256 ≤ x)
include hx

lemma xpos_of_large : 0 < x := lt_of_lt_of_le (Real.exp_pos _) hx

lemma log_ge_of_large : 256 ≤ Real.log x := by
  rw [← Real.log_exp 256]; exact Real.log_le_log (Real.exp_pos _) hx

/-- `log log x ≤ log x / 8`. -/
lemma loglog_le_of_large : Real.log (Real.log x) ≤ Real.log x / 8 := by
  have hL := log_ge_of_large hx
  have hL0 : 0 ≤ Real.log x := by linarith
  have h1 := Real.log_le_rpow_div hL0 (show (0:ℝ) < 1 / 2 by norm_num)
  rw [← Real.sqrt_eq_rpow] at h1
  have hs : 16 ≤ Real.sqrt (Real.log x) := by
    rw [Real.le_sqrt (by norm_num) hL0]; linarith
  have hss : Real.sqrt (Real.log x) * Real.sqrt (Real.log x) = Real.log x :=
    Real.mul_self_sqrt hL0
  have : Real.sqrt (Real.log x) / (1 / 2) ≤ Real.log x / 8 := by nlinarith
  linarith

/-- `1 ≤ log log x`. -/
lemma one_le_loglog_of_large : 1 ≤ Real.log (Real.log x) := by
  have hL := log_ge_of_large hx
  rw [← Real.log_exp 1]
  apply Real.log_le_log (Real.exp_pos _)
  have := Real.exp_one_lt_d9
  linarith

lemma log_div_sqrt_log_of_large :
    Real.log x / 4 ≤ Real.log (Real.sqrt x / Real.log x) := by
  have hx0 := xpos_of_large hx
  have hL := log_ge_of_large hx
  rw [Real.log_div (Real.sqrt_pos.mpr hx0).ne' (by linarith), Real.log_sqrt hx0.le]
  linarith [loglog_le_of_large hx]

lemma log_xi2_of_large : Real.log x / 4 ≤ Real.log (xi2 x) := by
  have hx0 := xpos_of_large hx
  have hL := log_ge_of_large hx
  rw [xi2, Real.log_div (Real.sqrt_pos.mpr hx0).ne' (by positivity), Real.log_sqrt hx0.le,
    Real.log_pow]
  push_cast
  linarith [loglog_le_of_large hx]

lemma two_le_xi2_of_large : 2 ≤ xi2 x := by
  have hx0 := xpos_of_large hx
  have hL := log_ge_of_large hx
  have hpos : 0 < xi2 x := by rw [xi2]; positivity
  have h := log_xi2_of_large hx
  have hlog2 : Real.log 2 < 1 := by
    have := Real.log_two_lt_d9; linarith
  rw [← Real.log_le_log_iff (by norm_num) hpos]
  linarith

end Estimates

/-- For a prime `q ≤ ξ₃` and `x ≥ e^256`: `π(x; q, 1) ≤ 160000 · x / (q log x)`. -/
lemma primeCountAP_le_of_le_xi3 {x : ℝ} (hx : Real.exp 256 ≤ x) {q : ℕ} (hq : q.Prime)
    (hq3 : (q : ℝ) ≤ xi3 x) :
    (primeCountAP q x : ℝ) ≤ 160000 * x / (q * Real.log x) := by
  have hx0 := xpos_of_large hx
  have hL := log_ge_of_large hx
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq.pos
  have hq2 : (2 : ℝ) ≤ q := by exact_mod_cast hq.two_le
  -- `log(x/q) ≥ log x / 4`
  have hxq : Real.sqrt x / Real.log x ≤ x / q := by
    rw [div_le_div_iff₀ (by linarith) hq0]
    have hxx : Real.sqrt x * Real.sqrt x = x := Real.mul_self_sqrt hx0.le
    have : Real.sqrt x * q ≤ Real.sqrt x * (Real.sqrt x * Real.log x) :=
      mul_le_mul_of_nonneg_left hq3 (Real.sqrt_nonneg x)
    nlinarith
  have hlogxq : Real.log x / 4 ≤ Real.log (x / q) :=
    (log_div_sqrt_log_of_large hx).trans
      (Real.log_le_log (div_pos (Real.sqrt_pos.mpr hx0) (by linarith)) hxq)
  have hqx : (q : ℝ) < x := by
    have : 0 < Real.log (x / q) := by linarith
    have := (Real.log_pos_iff (by positivity)).mp this
    rwa [one_lt_div hq0] at this
  have hbt := primeCountAP_le q hq.one_lt.le x hqx
  have htot : (q : ℝ) / 2 ≤ q.totient := by
    rw [Nat.totient_prime hq, Nat.cast_sub hq.one_lt.le]
    push_cast
    linarith
  calc (primeCountAP q x : ℝ) ≤ 20000 * x / (q.totient * Real.log (x / q)) := hbt
    _ ≤ 20000 * x / ((q / 2) * (Real.log x / 4)) := by
        apply div_le_div_of_nonneg_left (by positivity) (by positivity)
        exact mul_le_mul htot hlogxq (by positivity) (by positivity)
    _ = 160000 * x / (q * Real.log x) := by
        field_simp
        ring

/-- `∑_{ξ₂ < q ≤ ξ₃} 1/q ≤ 144 log log x / log x` for `x ≥ e^256`. -/
lemma sum_inv_largePrimes_le {x : ℝ} (hx : Real.exp 256 ≤ x) :
    ∑ q ∈ largePrimes x, (q : ℝ)⁻¹ ≤ 144 * Real.log (Real.log x) / Real.log x := by
  have hx0 := xpos_of_large hx
  have hL := log_ge_of_large hx
  have hl1 := one_le_loglog_of_large hx
  set L := Real.log x with hLdef
  set l := Real.log L with hldef
  have hA := two_le_xi2_of_large hx
  have hlogA := log_xi2_of_large hx
  have hlog2 := Real.log_two_gt_d9
  set J := ⌈3 * l / Real.log 2⌉₊ with hJ
  -- `2^J ≥ L^3`, so `ξ₂ 2^J ≥ ξ₃`
  have hJ1 : 3 * l / Real.log 2 ≤ J := Nat.le_ceil _
  have hpowJ : L ^ 3 ≤ (2 : ℝ) ^ J := by
    have h1 : L ^ 3 = Real.exp (3 * l) := by
      rw [hldef, mul_comm, Real.exp_mul, Real.exp_log (by linarith)]
      norm_cast
    have h2 : (2 : ℝ) ^ J = Real.exp (Real.log 2 * J) := by
      rw [← Real.rpow_natCast, Real.rpow_def_of_pos (by norm_num)]
    rw [h1, h2, Real.exp_le_exp]
    rw [div_le_iff₀ (by linarith)] at hJ1
    linarith
  have hcover : xi3 x ≤ xi2 x * 2 ^ J := by
    rw [xi2, xi3]
    have hL2 : 0 < L ^ 2 := by positivity
    rw [div_mul_eq_mul_div, le_div_iff₀ hL2]
    have : Real.sqrt x * L * L ^ 2 = Real.sqrt x * L ^ 3 := by ring
    rw [this]
    exact mul_le_mul_of_nonneg_left hpowJ (Real.sqrt_nonneg x)
  have hsub : largePrimes x ⊆ (Ioc ⌊xi2 x⌋₊ ⌊xi2 x * 2 ^ J⌋₊).filter Nat.Prime := by
    intro q hq
    simp only [largePrimes, mem_filter, mem_Ioc] at hq ⊢
    exact ⟨⟨hq.1.1, hq.1.2.trans (Nat.floor_mono hcover)⟩, hq.2⟩
  have hJle : (J : ℝ) ≤ 6 * l := by
    have := Nat.ceil_lt_add_one (show 0 ≤ 3 * l / Real.log 2 by positivity)
    rw [← hJ] at this
    have h5 : 3 * l / Real.log 2 ≤ 5 * l := by
      rw [div_le_iff₀ (by linarith)]; nlinarith
    linarith
  have hlog4 : Real.log 4 ≤ 3 := by
    have := Real.log_le_sub_one_of_pos (show (0:ℝ) < 4 by norm_num); linarith
  calc ∑ q ∈ largePrimes x, (q : ℝ)⁻¹
      ≤ ∑ q ∈ (Ioc ⌊xi2 x⌋₊ ⌊xi2 x * 2 ^ J⌋₊).filter Nat.Prime, (q : ℝ)⁻¹ :=
        sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => by positivity
    _ ≤ J * (2 * Real.log 4 / Real.log (xi2 x)) := sum_inv_primes_le hA J
    _ ≤ (6 * l) * (2 * 3 / (L / 4)) := by
        gcongr
        have : 0 < Real.log (xi2 x) := by linarith
        positivity
    _ = 144 * l / L := by
        have : L ≠ 0 := by linarith
        field_simp
        ring

/-- **Large primes (blueprint B3).** For `x ≥ e^256`,
`∑_{ξ₂ < q ≤ ξ₃, q prime} π(x; q, 1) ≤ 23040000 · x log log x / log² x`. -/
theorem largePrimesSum_le {x : ℝ} (hx : Real.exp 256 ≤ x) :
    (largePrimesSum x : ℝ) ≤ 23040000 * x * Real.log (Real.log x) / Real.log x ^ 2 := by
  have hx0 := xpos_of_large hx
  have hL := log_ge_of_large hx
  have hL0 : 0 < Real.log x := by linarith
  rw [largePrimesSum, Nat.cast_sum]
  calc ∑ q ∈ largePrimes x, (primeCountAP q x : ℝ)
      ≤ ∑ q ∈ largePrimes x, 160000 * x / Real.log x * (q : ℝ)⁻¹ := by
        refine sum_le_sum fun q hq => ?_
        simp only [largePrimes, mem_filter, mem_Ioc] at hq
        have hq3 : (q : ℝ) ≤ xi3 x := by
          have hxi3 : 0 ≤ xi3 x := by rw [xi3]; positivity
          exact (Nat.le_floor_iff hxi3).mp hq.1.2
        calc (primeCountAP q x : ℝ) ≤ 160000 * x / (q * Real.log x) :=
              primeCountAP_le_of_le_xi3 hx hq.2 hq3
          _ = 160000 * x / Real.log x * (q : ℝ)⁻¹ := by
              have : (q : ℝ) ≠ 0 := by exact_mod_cast hq.2.ne_zero
              field_simp
    _ = 160000 * x / Real.log x * ∑ q ∈ largePrimes x, (q : ℝ)⁻¹ := by rw [mul_sum]
    _ ≤ 160000 * x / Real.log x * (144 * Real.log (Real.log x) / Real.log x) := by
        gcongr
        exact sum_inv_largePrimes_le hx
    _ = 23040000 * x * Real.log (Real.log x) / Real.log x ^ 2 := by
        field_simp
        ring

/-- `x / log x ≤ (2 / log 2) π(x)` for `x ≥ 4`. -/
lemma div_log_le_primeCounting {x : ℝ} (hx : 4 ≤ x) :
    x / Real.log x ≤ 2 / Real.log 2 * (Nat.primeCounting ⌊x⌋₊ : ℝ) := by
  have hn : 4 ≤ ⌊x⌋₊ := Nat.le_floor (by exact_mod_cast hx)
  have hpi := Chebyshev.pi_ge_of_four_le hn
  have hn4 : (4 : ℝ) ≤ ⌊x⌋₊ := by exact_mod_cast hn
  have hlogn : 0 < Real.log ⌊x⌋₊ := Real.log_pos (by linarith)
  have hlogx : Real.log ⌊x⌋₊ ≤ Real.log x := Real.log_le_log (by linarith) (Nat.floor_le (by linarith))
  have hfl : x ≤ 2 * ⌊x⌋₊ := by linarith [Nat.lt_floor_add_one x]
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  calc x / Real.log x ≤ 2 * ⌊x⌋₊ / Real.log ⌊x⌋₊ := by
        apply div_le_div₀ (by positivity) hfl hlogn hlogx
    _ = 2 / Real.log 2 * (⌊x⌋₊ * Real.log 2 / Real.log ⌊x⌋₊) := by field_simp
    _ ≤ 2 / Real.log 2 * (Nat.primeCounting ⌊x⌋₊ : ℝ) := by gcongr

/-- `x log log x / log² x = o(x / log x)`. -/
lemma isLittleO_loglog_div_log_sq :
    (fun x : ℝ => x * Real.log (Real.log x) / Real.log x ^ 2) =o[atTop]
      fun x => x / Real.log x := by
  have h := (Real.isLittleO_log_id_atTop.comp_tendsto Real.tendsto_log_atTop).mul_isBigO
    (isBigO_refl (fun x : ℝ => x / Real.log x ^ 2) atTop)
  refine h.congr' (Eventually.of_forall fun x => ?_) ?_
  · simp only [Function.comp_apply]; ring
  · filter_upwards [eventually_gt_atTop 1] with x hx
    have : Real.log x ≠ 0 := (Real.log_pos hx).ne'
    simp only [Function.comp_apply, id]
    field_simp

/-- The large-prime range contributes `o(π(x))`. -/
theorem largePrimesSum_isLittleO :
    (fun x : ℝ => (largePrimesSum x : ℝ)) =o[atTop]
      fun x => (Nat.primeCounting ⌊x⌋₊ : ℝ) := by
  have h1 : (fun x : ℝ => (largePrimesSum x : ℝ)) =O[atTop]
      fun x => x * Real.log (Real.log x) / Real.log x ^ 2 := by
    refine IsBigO.of_bound 23040000 ?_
    filter_upwards [eventually_ge_atTop (Real.exp 256)] with x hx
    have hx0 := xpos_of_large hx
    have hL := log_ge_of_large hx
    have hl := one_le_loglog_of_large hx
    rw [Real.norm_of_nonneg (Nat.cast_nonneg _), Real.norm_of_nonneg (by positivity)]
    have := largePrimesSum_le hx
    calc (largePrimesSum x : ℝ) ≤ 23040000 * x * Real.log (Real.log x) / Real.log x ^ 2 := this
      _ = _ := by ring
  have h3 : (fun x : ℝ => x / Real.log x) =O[atTop]
      fun x => (Nat.primeCounting ⌊x⌋₊ : ℝ) := by
    refine IsBigO.of_bound (2 / Real.log 2) ?_
    filter_upwards [eventually_ge_atTop 4] with x hx
    have hlogx : 0 < Real.log x := Real.log_pos (by linarith)
    rw [Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (Nat.cast_nonneg _)]
    exact div_log_le_primeCounting hx
  exact h1.trans_isLittleO (isLittleO_loglog_div_log_sq.trans_isBigO h3)

/-! ### Hooley's large-prime count -/

open Classical in
/-- The number of primes `p < x`, `p ∤ a`, sifted out by some prime `q` with `ξ₂ < q ≤ ξ₃`:
`q ∣ p - 1` and `a^((p-1)/q) = 1` in `ZMod p`. -/
noncomputable def largePrimeCount (a : ℤ) (x : ℕ) : ℕ :=
  ((range x).filter fun p : ℕ => p.Prime ∧ ¬ (p : ℤ) ∣ a ∧
    ∃ q : ℕ, q.Prime ∧ xi2 x < q ∧ (q : ℝ) ≤ xi3 x ∧ q ∣ p - 1 ∧
      (a : ZMod p) ^ ((p - 1) / q) = 1).card

lemma largePrimeCount_le_largePrimesSum (a : ℤ) (x : ℕ) :
    largePrimeCount a x ≤ largePrimesSum x := by
  classical
  rw [largePrimeCount, largePrimesSum]
  refine (card_le_card ?_).trans card_biUnion_le
  intro p hp
  simp only [mem_filter, mem_range] at hp
  obtain ⟨hpx, hp, -, q, hq, hq2, hq3, hqd, -⟩ := hp
  simp only [mem_biUnion, largePrimes, mem_filter, mem_Ioc, mem_range, Nat.floor_natCast]
  have hxi2 : 0 ≤ xi2 x := by rw [xi2]; positivity
  have hxi3 : 0 ≤ xi3 x := le_trans (Nat.cast_nonneg q) hq3
  refine ⟨q, ⟨⟨(Nat.floor_lt hxi2).mpr hq2, Nat.le_floor hq3⟩, hq⟩, by omega, hp, ?_⟩
  exact ((Nat.modEq_iff_dvd' hp.one_lt.le).mpr hqd).symm

/-- **Large primes (blueprint B3), sieve form.** For `x ≥ e^256`, at most
`23040000 · x log log x / log² x` primes `p < x` are sifted out by a prime `q ∈ (ξ₂, ξ₃]`. -/
theorem largePrimeCount_le (a : ℤ) {x : ℕ} (hx : Real.exp 256 ≤ x) :
    (largePrimeCount a x : ℝ) ≤ 23040000 * x * Real.log (Real.log x) / Real.log x ^ 2 :=
  (Nat.cast_le.mpr (largePrimeCount_le_largePrimesSum a x)).trans (largePrimesSum_le hx)

/-- The primes sifted out by large primes are `o(π(x))`. -/
theorem largePrimeCount_isLittleO (a : ℤ) :
    (fun x : ℕ => (largePrimeCount a x : ℝ)) =o[atTop]
      fun x => (Nat.primeCounting x : ℝ) := by
  have h := largePrimesSum_isLittleO.comp_tendsto tendsto_natCast_atTop_atTop
  simp only [Function.comp_def, Nat.floor_natCast] at h
  refine IsBigO.trans_isLittleO (IsBigO.of_bound 1 (Eventually.of_forall fun x => ?_)) h
  rw [Real.norm_of_nonneg (Nat.cast_nonneg _), Real.norm_of_nonneg (Nat.cast_nonneg _), one_mul]
  exact_mod_cast largePrimeCount_le_largePrimesSum a x

end Artin
