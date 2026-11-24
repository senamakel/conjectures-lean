import Mertens.FareyDiscrete
import Mertens.Main

/-!
# Franel (1924) and Landau (1924) under RH

1. `integral_G_sq`: `∫₀¹ G² = 1/4 + (1/12) ∑_{q,r ≤ N} c_q c_r gcd(q,r)²/(qr)`, from the key
   integral and `∑_{q ≤ N} M(N/q) = 1`.
2. `sum_gcd_sq_le`: `∑_{q,r ≤ N} gcd(q,r)² (qr)^{-1-β} ≤ Z₁² Z₂` with `Z₁ = ∑ k^{-1-β}`,
   `Z₂ = ∑ d^{-2β}` (write `gcd² ≤ ∑_{d ∣ q, d ∣ r} d²`).
3. `card_farey_le`, `card_farey_ge`: `N²/8 ≤ A ≤ N²` (`#{coprime pairs ≤ N} = ∑ μ(d)⌊N/d⌋²
   ≥ 2N² − ∑ (N/d)² ≥ N²/4`).
4. With `|c_q| ≤ K 2^β N^β q^{-β}` (Mertens bound, `β = 1/2 + ε`): `∫₀¹ G² ≪ N^{2β}`,
   so `∑_f G(f)² ≪ N^{2+2β}` (`sum_G_sq_le`) and `∑_k δ_k² = A^{-2} ∑_f G(f)² ≪ N^{2β-2}`.
5. Landau: `(∑_k |δ_k|)² ≤ A ∑_k δ_k² ≪ N^{2β}` (Cauchy–Schwarz).
-/

namespace Mertens

open Finset MeasureTheory intervalIntegral Filter Asymptotics
open scoped ArithmeticFunction.Moebius

/-! ### Step 1 -/

lemma sum_fc {N : ℕ} (hN : 1 ≤ N) : ∑ q ∈ Ioc 0 N, fc N q = 1 := by
  have h := sum_mertens_div hN
  have h' : ((∑ q ∈ Ioc 0 N, mertens (N / q : ℕ) : ℤ) : ℝ) = 1 := by rw [h]; simp
  push_cast at h'
  exact h'

theorem integral_G_sq {N : ℕ} (hN : 1 ≤ N) :
    ∫ x in (0 : ℝ)..1, fareyG N x ^ 2 = 1 / 4 + (1 / 12) * ∑ q ∈ Ioc 0 N, ∑ r ∈ Ioc 0 N,
      fc N q * fc N r * ((Nat.gcd q r : ℝ) ^ 2 / (q * r)) := by
  have hexp : (fun x => fareyG N x ^ 2) = fun x => ∑ q ∈ Ioc 0 N, ∑ r ∈ Ioc 0 N,
      (fc N q * fc N r) * (Int.fract ((q : ℝ) * x) * Int.fract ((r : ℝ) * x)) := by
    funext x
    rw [sq, fareyG, sum_mul_sum]
    refine sum_congr rfl fun q _ => sum_congr rfl fun r _ => ?_
    ring
  have hii : ∀ q r : ℕ, IntervalIntegrable (fun x : ℝ =>
      (fc N q * fc N r) * (Int.fract ((q : ℝ) * x) * Int.fract ((r : ℝ) * x))) volume 0 1 :=
    fun q r => (show IntervalIntegrable (fun x : ℝ => Int.fract ((q : ℝ) * x) *
      Int.fract ((r : ℝ) * x)) volume 0 1 by simpa using ii_fract_mul q 0 r 0 0 1).const_mul _
  rw [hexp, intervalIntegral.integral_finsetSum (s := Ioc 0 N)
    (f := fun (q : ℕ) (x : ℝ) => ∑ r ∈ Ioc 0 N,
      (fc N q * fc N r) * (Int.fract ((q : ℝ) * x) * Int.fract ((r : ℝ) * x)))
    (fun q _ => ii_finset_sum (Ioc 0 N) fun r _ => hii q r)]
  have h2 : ∀ q ∈ Ioc 0 N, ∫ x in (0 : ℝ)..1, ∑ r ∈ Ioc 0 N,
      (fc N q * fc N r) * (Int.fract ((q : ℝ) * x) * Int.fract ((r : ℝ) * x)) =
        ∑ r ∈ Ioc 0 N, (fc N q * fc N r) * (1 / 4 + (Nat.gcd q r : ℝ) ^ 2 / (12 * q * r)) := by
    intro q hq
    rw [intervalIntegral.integral_finsetSum fun r _ => hii q r]
    refine sum_congr rfl fun r hr => ?_
    rw [intervalIntegral.integral_const_mul,
      integral_fract_mul_fract_mul (mem_Ioc.1 hq).1 (mem_Ioc.1 hr).1]
  rw [sum_congr rfl h2]
  have h3 : ∑ q ∈ Ioc 0 N, ∑ r ∈ Ioc 0 N,
      (fc N q * fc N r) * (1 / 4 + (Nat.gcd q r : ℝ) ^ 2 / (12 * q * r)) =
      (1 / 4) * ((∑ q ∈ Ioc 0 N, fc N q) * (∑ r ∈ Ioc 0 N, fc N r)) +
        (1 / 12) * ∑ q ∈ Ioc 0 N, ∑ r ∈ Ioc 0 N,
          fc N q * fc N r * ((Nat.gcd q r : ℝ) ^ 2 / (q * r)) := by
    rw [sum_mul_sum, mul_sum, mul_sum, ← sum_add_distrib]
    refine sum_congr rfl fun q _ => ?_
    rw [mul_sum, mul_sum, ← sum_add_distrib]
    refine sum_congr rfl fun r _ => ?_
    field_simp
    try ring
  rw [h3, sum_fc hN]
  ring

/-! ### Step 2 -/

/-- `∑_{q ≤ N, d ∣ q} q^{-γ} ≤ d^{-γ} ∑_k k^{-γ}`. -/
lemma sum_dvd_rpow_le {γ : ℝ} (hγ : 1 < γ) (N d : ℕ) :
    ∑ q ∈ Ioc 0 N, (if d ∣ q then (q : ℝ) ^ (-γ) else 0) ≤
      (d : ℝ) ^ (-γ) * ∑' k : ℕ, (k : ℝ) ^ (-γ) := by
  classical
  have hsum : Summable fun k : ℕ => (k : ℝ) ^ (-γ) := Real.summable_nat_rpow.2 (by linarith)
  rw [← sum_filter]
  have hsub : (Ioc 0 N).filter (fun q => d ∣ q) ⊆ (Ioc 0 N).image fun k : ℕ => d * k := by
    intro q hq
    simp only [mem_filter, mem_Ioc] at hq
    obtain ⟨⟨h0, hN⟩, k, rfl⟩ := hq
    refine mem_image.2 ⟨k, mem_Ioc.2 ⟨?_, ?_⟩, rfl⟩
    · rcases Nat.eq_zero_or_pos k with rfl | h
      · simp at h0
      · exact h
    · exact le_trans (Nat.le_mul_of_pos_left k (Nat.pos_of_ne_zero (by rintro rfl; simp at h0)))
        hN
  calc ∑ q ∈ (Ioc 0 N).filter (fun q => d ∣ q), (q : ℝ) ^ (-γ)
      ≤ ∑ q ∈ (Ioc 0 N).image (fun k : ℕ => d * k), (q : ℝ) ^ (-γ) :=
        sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => by positivity
    _ ≤ ∑ k ∈ Ioc 0 N, ((d * k : ℕ) : ℝ) ^ (-γ) := sum_image_le_of_nonneg fun _ _ => by positivity
    _ = (d : ℝ) ^ (-γ) * ∑ k ∈ Ioc 0 N, (k : ℝ) ^ (-γ) := by
        rw [mul_sum]
        refine sum_congr rfl fun k _ => ?_
        push_cast
        rw [Real.mul_rpow (by positivity) (by positivity)]
    _ ≤ (d : ℝ) ^ (-γ) * ∑' k : ℕ, (k : ℝ) ^ (-γ) := by
        gcongr
        exact hsum.sum_le_tsum _ fun _ _ => by positivity

theorem sum_gcd_sq_le {β : ℝ} (hβ : 1 / 2 < β) (N : ℕ) :
    ∑ q ∈ Ioc 0 N, ∑ r ∈ Ioc 0 N,
        (Nat.gcd q r : ℝ) ^ 2 * ((q : ℝ) ^ (-(1 + β)) * (r : ℝ) ^ (-(1 + β))) ≤
      (∑' k : ℕ, (k : ℝ) ^ (-(1 + β))) ^ 2 * ∑' d : ℕ, (d : ℝ) ^ (-(2 * β)) := by
  classical
  set γ := 1 + β
  set w : ℕ → ℝ := fun q => (q : ℝ) ^ (-γ)
  set Z1 := ∑' k : ℕ, (k : ℝ) ^ (-γ)
  have hZ1 : 0 ≤ Z1 := tsum_nonneg fun _ => by positivity
  have hsum2 : Summable fun d : ℕ => (d : ℝ) ^ (-(2 * β)) := Real.summable_nat_rpow.2 (by linarith)
  -- `gcd² ≤ ∑_{d ∣ q, d ∣ r} d²`
  have hg : ∀ q ∈ Ioc 0 N, ∀ r ∈ Ioc 0 N, (Nat.gcd q r : ℝ) ^ 2 ≤
      ∑ d ∈ Ioc 0 N, (if d ∣ q ∧ d ∣ r then (d : ℝ) ^ 2 else 0) := by
    intro q hq r hr
    have hq0 : 0 < q := (mem_Ioc.1 hq).1
    have hmem : Nat.gcd q r ∈ Ioc 0 N :=
      mem_Ioc.2 ⟨Nat.gcd_pos_of_pos_left r hq0,
        le_trans (Nat.gcd_le_left r hq0) (mem_Ioc.1 hq).2⟩
    have := single_le_sum (f := fun d => if d ∣ q ∧ d ∣ r then (d : ℝ) ^ 2 else 0)
      (fun d _ => by positivity) hmem
    simpa [Nat.gcd_dvd_left, Nat.gcd_dvd_right] using this
  calc ∑ q ∈ Ioc 0 N, ∑ r ∈ Ioc 0 N, (Nat.gcd q r : ℝ) ^ 2 * (w q * w r)
      ≤ ∑ q ∈ Ioc 0 N, ∑ r ∈ Ioc 0 N,
          (∑ d ∈ Ioc 0 N, (if d ∣ q ∧ d ∣ r then (d : ℝ) ^ 2 else 0)) * (w q * w r) :=
        sum_le_sum fun q hq => sum_le_sum fun r hr =>
          mul_le_mul_of_nonneg_right (hg q hq r hr) (by positivity)
    _ = ∑ d ∈ Ioc 0 N, (d : ℝ) ^ 2 * ((∑ q ∈ Ioc 0 N, if d ∣ q then w q else 0) *
          (∑ r ∈ Ioc 0 N, if d ∣ r then w r else 0)) := by
        have e1 : ∀ q ∈ Ioc 0 N, ∑ r ∈ Ioc 0 N,
            (∑ d ∈ Ioc 0 N, (if d ∣ q ∧ d ∣ r then (d : ℝ) ^ 2 else 0)) * (w q * w r) =
            ∑ d ∈ Ioc 0 N, ∑ r ∈ Ioc 0 N,
              (if d ∣ q ∧ d ∣ r then (d : ℝ) ^ 2 else 0) * (w q * w r) := fun q _ => by
          simp_rw [sum_mul]
          exact sum_comm
        rw [sum_congr rfl e1, sum_comm]
        refine sum_congr rfl fun d _ => ?_
        rw [sum_mul_sum, mul_sum]
        refine sum_congr rfl fun q _ => ?_
        rw [mul_sum]
        refine sum_congr rfl fun r _ => ?_
        by_cases hq : d ∣ q <;> by_cases hr : d ∣ r <;> simp [hq, hr] <;> (try ring)
    _ ≤ ∑ d ∈ Ioc 0 N, (d : ℝ) ^ 2 * (((d : ℝ) ^ (-γ) * Z1) * ((d : ℝ) ^ (-γ) * Z1)) := by
        refine sum_le_sum fun d _ => ?_
        have h1 := sum_dvd_rpow_le (γ := γ) (by linarith) N d
        have h0 : 0 ≤ ∑ q ∈ Ioc 0 N, (if d ∣ q then w q else 0) :=
          sum_nonneg fun q _ => by split_ifs <;> positivity
        gcongr
    _ = Z1 ^ 2 * ∑ d ∈ Ioc 0 N, (d : ℝ) ^ (-(2 * β)) := by
        rw [mul_sum]
        refine sum_congr rfl fun d hd => ?_
        have hd0 : (0 : ℝ) < d := by exact_mod_cast (mem_Ioc.1 hd).1
        have : (d : ℝ) ^ 2 * ((d : ℝ) ^ (-γ) * (d : ℝ) ^ (-γ)) = (d : ℝ) ^ (-(2 * β)) := by
          rw [← Real.rpow_add hd0, ← Real.rpow_natCast, ← Real.rpow_add hd0]
          congr 1
          simp only [γ]; push_cast; ring
        rw [← this]; ring
    _ ≤ Z1 ^ 2 * ∑' d : ℕ, (d : ℝ) ^ (-(2 * β)) := by
        gcongr
        exact hsum2.sum_le_tsum _ fun _ _ => by positivity

/-! ### Step 3: `N²/8 ≤ A ≤ N²` -/

lemma sum_inv_sq_le (N : ℕ) : ∑ d ∈ Ioc 0 N, (1 : ℝ) / (d : ℝ) ^ 2 ≤ 7 / 4 := by
  have key : ∀ n : ℕ, 2 ≤ n → ∑ d ∈ Ioc 0 n, (1 : ℝ) / (d : ℝ) ^ 2 ≤ 7 / 4 - 1 / (n : ℝ) := by
    intro n hn
    induction n, hn using Nat.le_induction with
    | base =>
      rw [show Ioc 0 2 = {1, 2} from by decide]
      norm_num
    | succ n hn ih =>
      rw [sum_Ioc_succ_top (by omega)]
      have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
      have h : (1 : ℝ) / ((n : ℝ) + 1) ^ 2 ≤ 1 / n - 1 / ((n : ℝ) + 1) := by
        rw [div_sub_div _ _ (ne_of_gt hn0) (by positivity), div_le_div_iff₀ (by positivity)
          (by positivity)]
        nlinarith
      push_cast
      linarith
  rcases Nat.lt_or_ge N 2 with h | h
  · interval_cases N
    · norm_num
    · rw [show Ioc 0 1 = {1} from by decide]; norm_num
  · have := key N h
    have : (0 : ℝ) ≤ 1 / N := by positivity
    linarith

lemma card_farey_le (N : ℕ) : ((farey N).card : ℝ) ≤ (N : ℝ) ^ 2 := by
  have : (farey N).card ≤ N * N := by
    refine card_image_le.trans ((card_filter_le _ _).trans ?_)
    simp [card_product]
  have h' : ((farey N).card : ℝ) ≤ ((N * N : ℕ) : ℝ) := by exact_mod_cast this
  push_cast at h'
  nlinarith

/-- All coprime pairs `(p, q)` with `1 ≤ p, q ≤ N`. -/
def allCoprime (N : ℕ) : Finset (ℕ × ℕ) :=
  (Ioc 0 N ×ˢ Ioc 0 N).filter fun pq => pq.1.Coprime pq.2

lemma card_farey_eq_pairs (N : ℕ) : (farey N).card = (coprimePairs N 1).card := by
  have h := fareyFilter_eq_image (N := N) (x := 1) le_rfl
  have hall : (farey N).filter (fun f : ℚ => (f : ℝ) ≤ 1) = farey N :=
    filter_true_of_mem fun f hf => by exact_mod_cast (mem_farey.1 hf).2.1
  rw [hall] at h
  rw [h, card_image_of_injOn (coprimePairs_injOn N 1)]

lemma card_allCoprime_le (N : ℕ) : (allCoprime N).card ≤ 2 * (farey N).card := by
  rw [card_farey_eq_pairs]
  have hsub : allCoprime N ⊆ coprimePairs N 1 ∪ (coprimePairs N 1).image (Prod.swap : ℕ × ℕ → ℕ × ℕ) := by
    rintro ⟨p, q⟩ hpq
    simp only [allCoprime, mem_filter, mem_product] at hpq
    obtain ⟨⟨hp, hq⟩, hc⟩ := hpq
    rcases le_total p q with h | h
    · refine mem_union_left _ ?_
      simp only [coprimePairs, mem_filter, mem_product, mul_one]
      exact ⟨⟨hp, hq⟩, hc, by exact_mod_cast h⟩
    · refine mem_union_right _ (mem_image.2 ⟨(q, p), ?_, rfl⟩)
      simp only [coprimePairs, mem_filter, mem_product, mul_one]
      exact ⟨⟨hq, hp⟩, hc.symm, by exact_mod_cast h⟩
  calc (allCoprime N).card ≤ (coprimePairs N 1 ∪ (coprimePairs N 1).image (Prod.swap : ℕ × ℕ → ℕ × ℕ)).card :=
        card_le_card hsub
    _ ≤ (coprimePairs N 1).card + ((coprimePairs N 1).image (Prod.swap : ℕ × ℕ → ℕ × ℕ)).card := card_union_le _ _
    _ ≤ (coprimePairs N 1).card + (coprimePairs N 1).card := by
        have := card_image_le (s := coprimePairs N 1) (f := (Prod.swap : ℕ × ℕ → ℕ × ℕ)); omega
    _ = 2 * (coprimePairs N 1).card := by ring

lemma card_allCoprime_eq (N : ℕ) :
    ((allCoprime N).card : ℤ) = ∑ d ∈ Ioc 0 N, μ d * ((N / d : ℕ) : ℤ) ^ 2 := by
  classical
  have h1 : (allCoprime N).card = ∑ q ∈ Ioc 0 N, #{p ∈ Ioc 0 N | p.Coprime q} := by
    rw [allCoprime, card_filter, sum_product_right]
    refine sum_congr rfl fun q _ => ?_
    rw [card_filter]
  rw [h1]
  push_cast
  have h2 : ∀ q ∈ Ioc 0 N, ((#{p ∈ Ioc 0 N | p.Coprime q} : ℕ) : ℤ) =
      ∑ d ∈ Ioc 0 N, if d ∣ q then μ d * ((N / d : ℕ) : ℤ) else 0 := by
    intro q hq
    have hq0 : q ≠ 0 := by simp at hq; omega
    rw [card_coprime_Ioc N hq0, ← sum_filter]
    congr 1
    ext d
    simp only [Nat.mem_divisors, mem_filter, mem_Ioc]
    constructor
    · rintro ⟨hd, -⟩
      have := Nat.pos_of_dvd_of_pos hd (Nat.pos_of_ne_zero hq0)
      exact ⟨⟨this, le_trans (Nat.le_of_dvd (Nat.pos_of_ne_zero hq0) hd) (mem_Ioc.1 hq).2⟩, hd⟩
    · rintro ⟨-, hd⟩; exact ⟨hd, hq0⟩
  rw [sum_congr rfl h2, sum_comm]
  refine sum_congr rfl fun d _ => ?_
  rw [← sum_filter, sum_const, Nat.Ioc_filter_dvd_card_eq_div, nsmul_eq_mul]
  push_cast
  ring

lemma card_farey_ge {N : ℕ} (hN : 1 ≤ N) : (N : ℝ) ^ 2 / 8 ≤ (farey N).card := by
  have hP : (N : ℝ) ^ 2 / 4 ≤ (allCoprime N).card := by
    have h := card_allCoprime_eq N
    have h' : ((allCoprime N).card : ℝ) = ∑ d ∈ Ioc 0 N, (μ d : ℝ) * ((N / d : ℕ) : ℝ) ^ 2 := by
      have := congrArg (fun z : ℤ => (z : ℝ)) h
      push_cast at this
      exact this
    rw [h']
    have hterm : ∀ d ∈ Ioc 0 N, (if d = 1 then 2 * (N : ℝ) ^ 2 else 0) - (N : ℝ) ^ 2 * (1 / (d : ℝ) ^ 2)
        ≤ (μ d : ℝ) * ((N / d : ℕ) : ℝ) ^ 2 := by
      intro d hd
      have hd0 : (0 : ℝ) < d := by exact_mod_cast (mem_Ioc.1 hd).1
      have hq : ((N / d : ℕ) : ℝ) ^ 2 ≤ (N : ℝ) ^ 2 * (1 / (d : ℝ) ^ 2) := by
        have h1 : ((N / d : ℕ) : ℝ) ≤ (N : ℝ) / d := Nat.cast_div_le
        calc ((N / d : ℕ) : ℝ) ^ 2 ≤ ((N : ℝ) / d) ^ 2 := by gcongr
          _ = (N : ℝ) ^ 2 * (1 / (d : ℝ) ^ 2) := by ring
      by_cases h1 : d = 1
      · subst h1
        simp
        nlinarith
      · rw [if_neg h1, zero_sub]
        have hμ : (-1 : ℝ) ≤ μ d := by
          have := ArithmeticFunction.abs_moebius_le_one (n := d)
          have : (-1 : ℤ) ≤ μ d := (abs_le.1 this).1
          exact_mod_cast this
        nlinarith [sq_nonneg ((N / d : ℕ) : ℝ)]
    calc (N : ℝ) ^ 2 / 4 ≤ 2 * (N : ℝ) ^ 2 - (N : ℝ) ^ 2 * (7 / 4) := by nlinarith
      _ ≤ ∑ d ∈ Ioc 0 N, (if d = 1 then 2 * (N : ℝ) ^ 2 else 0) -
            (N : ℝ) ^ 2 * ∑ d ∈ Ioc 0 N, (1 / (d : ℝ) ^ 2) := by
          rw [sum_ite_eq', if_pos (mem_Ioc.2 ⟨one_pos, hN⟩)]
          gcongr
          exact sum_inv_sq_le N
      _ = ∑ d ∈ Ioc 0 N, ((if d = 1 then 2 * (N : ℝ) ^ 2 else 0) -
            (N : ℝ) ^ 2 * (1 / (d : ℝ) ^ 2)) := by rw [sum_sub_distrib, mul_sum]
      _ ≤ _ := sum_le_sum hterm
  have h2 : ((allCoprime N).card : ℝ) ≤ 2 * (farey N).card := by
    exact_mod_cast card_allCoprime_le N
  linarith

/-! ### Step 4: Franel -/

/-- **Franel's bound from the Mertens bound**, quantitatively: for `β > 1/2`,
`∑_k δ_k² ≤ C N^{2β-2}`. -/
theorem franelL2_le (hMB : MertensBound) {β : ℝ} (hβ : 1 / 2 < β) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ, 1 ≤ N → franelL2 N ≤ C * (N : ℝ) ^ (2 * β - 2) := by
  obtain ⟨K, hK0, hK⟩ := abs_mertens_le_of_mertensBound hMB hβ
  set Z1 := ∑' k : ℕ, (k : ℝ) ^ (-(1 + β))
  set Z2 := ∑' d : ℕ, (d : ℝ) ^ (-(2 * β))
  have hZ1 : 0 ≤ Z1 := tsum_nonneg fun _ => by positivity
  have hZ2 : 0 ≤ Z2 := tsum_nonneg fun _ => by positivity
  set D : ℝ := (K * 2 ^ β) ^ 2 * Z1 ^ 2 * Z2
  have hD : 0 ≤ D := by positivity
  refine ⟨64 * (27 / 4 + D / 4), by positivity, fun N hN => ?_⟩
  have hNR : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < N := by linarith
  set X : ℝ := (N : ℝ) ^ β
  have hX1 : 1 ≤ X := Real.one_le_rpow hNR (by linarith)
  -- `|c_q| ≤ K 2^β X q^{-β}`
  have hc : ∀ q ∈ Ioc 0 N, |fc N q| ≤ K * 2 ^ β * X * (q : ℝ) ^ (-β) := by
    intro q hq
    have hq0 : (0 : ℝ) < q := by exact_mod_cast (mem_Ioc.1 hq).1
    have hqN : (q : ℝ) ≤ N := by exact_mod_cast (mem_Ioc.1 hq).2
    have h1 : ((N / q : ℕ) : ℝ) + 1 ≤ 2 * ((N : ℝ) / q) := by
      have := (Nat.cast_div_le : ((N / q : ℕ) : ℝ) ≤ (N : ℝ) / q)
      have : (1 : ℝ) ≤ (N : ℝ) / q := by rw [le_div_iff₀ hq0, one_mul]; exact hqN
      linarith
    calc |fc N q| ≤ K * (((N / q : ℕ) : ℝ) + 1) ^ β := hK _
      _ ≤ K * (2 * ((N : ℝ) / q)) ^ β := by gcongr
      _ = K * 2 ^ β * X * (q : ℝ) ^ (-β) := by
          rw [Real.mul_rpow (by norm_num) (by positivity), Real.div_rpow hN0.le hq0.le,
            Real.rpow_neg hq0.le]
          ring
  -- the double sum
  have hT : ∑ q ∈ Ioc 0 N, ∑ r ∈ Ioc 0 N, fc N q * fc N r * ((Nat.gcd q r : ℝ) ^ 2 / (q * r)) ≤
      D * X ^ 2 := by
    have hterm : ∀ q ∈ Ioc 0 N, ∀ r ∈ Ioc 0 N,
        fc N q * fc N r * ((Nat.gcd q r : ℝ) ^ 2 / (q * r)) ≤
          (K * 2 ^ β * X) ^ 2 * ((Nat.gcd q r : ℝ) ^ 2 *
            ((q : ℝ) ^ (-(1 + β)) * (r : ℝ) ^ (-(1 + β)))) := by
      intro q hq r hr
      have hq0 : (0 : ℝ) < q := by exact_mod_cast (mem_Ioc.1 hq).1
      have hr0 : (0 : ℝ) < r := by exact_mod_cast (mem_Ioc.1 hr).1
      have hg : 0 ≤ (Nat.gcd q r : ℝ) ^ 2 / (q * r) := by positivity
      have hqq : (q : ℝ) ^ (-(1 + β)) = (q : ℝ) ^ (-β) / q := by
        rw [show -(1 + β) = -β + (-1) by ring, Real.rpow_add hq0, Real.rpow_neg_one, div_eq_mul_inv]
      have hrr : (r : ℝ) ^ (-(1 + β)) = (r : ℝ) ^ (-β) / r := by
        rw [show -(1 + β) = -β + (-1) by ring, Real.rpow_add hr0, Real.rpow_neg_one, div_eq_mul_inv]
      calc fc N q * fc N r * ((Nat.gcd q r : ℝ) ^ 2 / (q * r))
          ≤ |fc N q * fc N r * ((Nat.gcd q r : ℝ) ^ 2 / (q * r))| := le_abs_self _
        _ = |fc N q| * |fc N r| * ((Nat.gcd q r : ℝ) ^ 2 / (q * r)) := by
            rw [abs_mul, abs_mul, abs_of_nonneg hg]
        _ ≤ (K * 2 ^ β * X * (q : ℝ) ^ (-β)) * (K * 2 ^ β * X * (r : ℝ) ^ (-β)) *
              ((Nat.gcd q r : ℝ) ^ 2 / (q * r)) := by
            gcongr
            · exact hc q hq
            · exact hc r hr
        _ = _ := by
            rw [hqq, hrr]
            field_simp
    calc _ ≤ ∑ q ∈ Ioc 0 N, ∑ r ∈ Ioc 0 N, (K * 2 ^ β * X) ^ 2 * ((Nat.gcd q r : ℝ) ^ 2 *
            ((q : ℝ) ^ (-(1 + β)) * (r : ℝ) ^ (-(1 + β)))) :=
          sum_le_sum fun q hq => sum_le_sum fun r hr => hterm q hq r hr
      _ = (K * 2 ^ β * X) ^ 2 * ∑ q ∈ Ioc 0 N, ∑ r ∈ Ioc 0 N, (Nat.gcd q r : ℝ) ^ 2 *
            ((q : ℝ) ^ (-(1 + β)) * (r : ℝ) ^ (-(1 + β))) := by
          rw [mul_sum]; simp_rw [mul_sum]
      _ ≤ (K * 2 ^ β * X) ^ 2 * (Z1 ^ 2 * Z2) := by
          gcongr
          exact sum_gcd_sq_le hβ N
      _ = D * X ^ 2 := by simp only [D]; ring
  have hI : ∫ x in (0 : ℝ)..1, fareyG N x ^ 2 ≤ 1 / 4 + (1 / 12) * (D * X ^ 2) := by
    rw [integral_G_sq hN]; linarith
  have hA1 := card_farey_le N
  have hA2 := card_farey_ge hN
  set A : ℝ := ((farey N).card : ℝ)
  have hA0 : 0 < A := by have : 0 < (N : ℝ) ^ 2 / 8 := by positivity
                         linarith
  have hS : ∑ f ∈ farey N, fareyG N f ^ 2 ≤ (27 / 4 + D / 4) * (N : ℝ) ^ 2 * X ^ 2 := by
    have h := sum_G_sq_le hN
    have hrest : A * (3 * A ^ 2 * (1 / (N : ℝ) ^ 2) ^ 2 + 3) ≤ 6 * (N : ℝ) ^ 2 := by
      have : A ^ 2 * (1 / (N : ℝ) ^ 2) ^ 2 ≤ 1 := by
        rw [← mul_pow, show A * (1 / (N : ℝ) ^ 2) = A / (N : ℝ) ^ 2 by ring]
        have : A / (N : ℝ) ^ 2 ≤ 1 := by rw [div_le_one (by positivity)]; exact hA1
        have h0 : 0 ≤ A / (N : ℝ) ^ 2 := by positivity
        nlinarith
      nlinarith
    have hX2 : 1 ≤ X ^ 2 := by nlinarith
    have hN2 : 0 ≤ (N : ℝ) ^ 2 := by positivity
    calc ∑ f ∈ farey N, fareyG N f ^ 2
        ≤ 3 * (N : ℝ) ^ 2 * (∫ x in (0 : ℝ)..1, fareyG N x ^ 2) +
            A * (3 * A ^ 2 * (1 / (N : ℝ) ^ 2) ^ 2 + 3) := h
      _ ≤ 3 * (N : ℝ) ^ 2 * (1 / 4 + (1 / 12) * (D * X ^ 2)) + 6 * (N : ℝ) ^ 2 := by
          gcongr
      _ ≤ (27 / 4 + D / 4) * (N : ℝ) ^ 2 * X ^ 2 := by nlinarith
  rw [franelL2_eq]
  have hsum : ∑ f ∈ farey N, (fareyG N f / A) ^ 2 = (∑ f ∈ farey N, fareyG N f ^ 2) / A ^ 2 := by
    rw [sum_div]; simp_rw [div_pow]
  rw [hsum]
  have hpow : (N : ℝ) ^ (2 * β - 2) = X ^ 2 / (N : ℝ) ^ 2 := by
    rw [Real.rpow_sub hN0, show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast,
      show ((2 : ℕ) : ℝ) * β = β * ((2 : ℕ) : ℝ) by ring, Real.rpow_mul hN0.le, Real.rpow_natCast]
  rw [hpow, div_le_iff₀ (by positivity)]
  have hA8 : (N : ℝ) ^ 4 ≤ 64 * A ^ 2 := by nlinarith
  calc ∑ f ∈ farey N, fareyG N f ^ 2 ≤ (27 / 4 + D / 4) * (N : ℝ) ^ 2 * X ^ 2 := hS
    _ = (27 / 4 + D / 4) * X ^ 2 / (N : ℝ) ^ 2 * (N : ℝ) ^ 4 := by field_simp
    _ ≤ (27 / 4 + D / 4) * X ^ 2 / (N : ℝ) ^ 2 * (64 * A ^ 2) := by gcongr
    _ = 64 * (27 / 4 + D / 4) * (X ^ 2 / (N : ℝ) ^ 2) * A ^ 2 := by ring

/-- **Franel (1924), from the Mertens bound**: `∑_k (f_k − k/A)² = O(N^{−1+ε})`. -/
theorem franel_of_mertensBound (hMB : MertensBound) : FranelBound := by
  intro ε hε
  obtain ⟨C, hC0, hC⟩ := franelL2_le hMB (β := 1 / 2 + ε / 2) (by linarith)
  refine IsBigO.of_bound C ?_
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hN0 : (0 : ℝ) ≤ N := N.cast_nonneg
  have h0 : 0 ≤ franelL2 N := by rw [franelL2]; positivity
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg h0, abs_of_nonneg (Real.rpow_nonneg hN0 _)]
  have := hC N hN
  rwa [show 2 * (1 / 2 + ε / 2) - 2 = -1 + ε by ring] at this

/-- **Landau (1924), from the Mertens bound**: `∑_k |f_k − k/A| = O(N^{1/2+ε})`. -/
theorem franelLandau_of_mertensBound (hMB : MertensBound) : FranelLandauBound := by
  intro ε hε
  obtain ⟨C, hC0, hC⟩ := franelL2_le hMB (β := 1 / 2 + ε) (by linarith)
  refine IsBigO.of_bound (Real.sqrt C) ?_
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hNR : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < N := by linarith
  have h0 : 0 ≤ franelL1 N := by rw [franelL1]; positivity
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg h0, abs_of_nonneg (Real.rpow_nonneg hN0.le _)]
  have hCS : franelL1 N ^ 2 ≤ (farey N).card * franelL2 N := by
    rw [franelL1_eq, franelL2_eq]
    have := sq_sum_le_card_mul_sum_sq (s := farey N) (f := fun f => |fareyG N f / (farey N).card|)
    simpa only [sq_abs] using this
  have hL2 := hC N hN
  have hA := card_farey_le N
  have h2 : franelL1 N ^ 2 ≤ (Real.sqrt C * (N : ℝ) ^ (1 / 2 + ε)) ^ 2 := by
    have hL20 : 0 ≤ franelL2 N := by rw [franelL2]; positivity
    calc franelL1 N ^ 2 ≤ (farey N).card * franelL2 N := hCS
      _ ≤ (N : ℝ) ^ 2 * (C * (N : ℝ) ^ (2 * (1 / 2 + ε) - 2)) := by gcongr
      _ = (Real.sqrt C * (N : ℝ) ^ (1 / 2 + ε)) ^ 2 := by
          rw [mul_pow, Real.sq_sqrt hC0, ← Real.rpow_natCast ((N : ℝ) ^ (1 / 2 + ε)),
            ← Real.rpow_mul hN0.le, Real.rpow_sub hN0, show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num,
            Real.rpow_natCast]
          field_simp
  exact (pow_le_pow_iff_left₀ h0 (by positivity) two_ne_zero).1 h2

/-- **Franel (1924) under RH**: `∑_k (f_k − k/A)² = O(N^{−1+ε})`. -/
theorem franel_of_RH (hRH : RiemannHypothesis) : FranelBound :=
  franel_of_mertensBound (mertens_of_RH hRH)

/-- **Landau (1924) under RH**: `∑_k |f_k − k/A| = O(N^{1/2+ε})`. -/
theorem franelLandau_of_RH (hRH : RiemannHypothesis) : FranelLandauBound :=
  franelLandau_of_mertensBound (mertens_of_RH hRH)

end Mertens
