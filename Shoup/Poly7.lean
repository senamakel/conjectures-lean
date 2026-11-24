import Shoup.Sieve.Thresholds

/-!
# `PolyOmegaStatement 7`: `g(p) ≤ C ω(p-1)^7 (log p)²` under GRH

Write `m = ω(p - 1)`, `P` for the prime factors of `p - 1`, and choose `n` least with
`1000 m ≤ 2^{1000 n}`; for `m ≥ 2^{1000 · 2^{23}}` this forces `n ≥ 2^{23}`. Thresholds (as
exponents of `2`, in units of `n`): `1000 → 485 → 240 → 138 → 47 → 19 → 5`, then halving
`5n, 5n/2, 5n/4, …` until the exponent drops below `2^{21}`.

* top block `ℓ > 2^{485 n}`: level 1 (union bound), ratio `Σ 1/ℓ ≤ log(200/97) + …`;
* five blocks of levels `3, 3, 5, 5, 7` between `2^{5n}` and `2^{485 n}`;
* halving blocks `(2^{5n/2^{i+1}}, 2^{5n/2^i}]` of level `2i + 7`;
* an exact bottom block (all primes below `2^{2^{21}}`).

Mertens (`Shoup.Sieve.Mertens`) bounds each block's `Σ 1/ℓ` by `log` of the exponent ratio plus
a small error; Maclaurin gives `e_k/U_k ≤ σ^k/k! · e^{(1+η)σ}`. The ratios sum to `≤ 24/25`
(`ratioSumU_le`). The mass is `(1 + m) · 2^{2390 n + O(1)}` and
`∏_{ℓ ∈ P} (1 - 1/ℓ) ≥ c · 2^{-n}`, so the sieve inequality gives
`x ≤ C m² 2^{4782 n} (log p)² ≤ C' m^7 (log p)²` since `2^{1000 n} ≤ 2^{1000} · 1000 m`.
Small `m` are covered by `polyOmega_of_GRH : PolyOmegaStatement 136`.
-/

namespace Shoup.Sieve

open Finset ArithmeticFunction Erdos985
open scoped ArithmeticFunction.omega

/-! ### The design -/

/-- The bottom threshold `U = 2^{20}`. -/
irreducible_def Ubot : ℕ := 2 ^ 20

/-- Custom thresholds `1000, 485, 240, 138, 47, 19, 5`: index `0` is `485`. -/
def ks : ℕ → ℕ
  | 0 => 485
  | 1 => 240
  | 2 => 138
  | 3 => 47
  | 4 => 19
  | _ => 5

/-- Custom levels (degree `2 k + 1`): `3, 3, 5, 5, 7`. -/
def kc : ℕ → ℕ
  | 0 => 1
  | 1 => 1
  | 2 => 2
  | 3 => 2
  | _ => 3

def eT (n : ℕ) (i : ℕ) : ℕ := if i ≤ 5 then n * ks i else 5 * n / 2 ^ (i - 5)

def levT (i : ℕ) : ℕ := if i < 5 then kc i else i - 2

/-- The number of halving blocks. -/
def Tn (n : ℕ) : ℕ := Nat.log 2 (5 * n / Ubot)

def Kn (n : ℕ) : ℕ := 5 + Tn n

/-- The bottom level: `2 kbot + 1 > 2^{2 U}`. -/
def kbot : ℕ := 2 ^ (2 * Ubot)

def bsT (P : Finset ℕ) (n : ℕ) : List Block := blocksT P (eT n) levT (Kn n) kbot

lemma eT_five (n : ℕ) : eT n 5 = 5 * n := by simp [eT, ks]; ring

lemma eT_tail (n i : ℕ) : eT n (5 + i) = 5 * n / 2 ^ i := by
  rcases Nat.eq_zero_or_pos i with rfl | hi
  · simp [eT, ks]; ring
  · simp only [eT]; rw [if_neg (show ¬ (5 + i ≤ 5) by omega)]; congr 2; omega

lemma eT_anti (n : ℕ) : ∀ i < Kn n, eT n (i + 1) ≤ eT n i := by
  intro i _
  rcases lt_or_ge i 5 with h | h
  · interval_cases i <;> simp [eT, ks] <;> omega
  · obtain ⟨j, rfl⟩ : ∃ j, i = 5 + j := ⟨i - 5, by omega⟩
    rw [show 5 + j + 1 = 5 + (j + 1) by ring, eT_tail, eT_tail, pow_succ, ← Nat.div_div_eq_div_mul]
    exact Nat.div_le_self _ _

lemma Tn_facts (n : ℕ) (hn : 2 ^ 23 ≤ n) :
    Ubot * 2 ^ Tn n ≤ 5 * n ∧ 5 * n < 2 * Ubot * 2 ^ Tn n := by
  have hU : 0 < Ubot := by rw [Ubot_def]; positivity
  set q := 5 * n / Ubot with hq
  have hq0 : q ≠ 0 := by
    rw [hq]; apply Nat.div_ne_zero_iff.mpr
    rw [Ubot_def]; omega
  have h1 : 2 ^ Tn n ≤ q := Nat.pow_log_le_self 2 hq0
  have h2 : q < 2 ^ (Tn n + 1) := Nat.lt_pow_succ_log_self (by norm_num) q
  have h3 : q * Ubot ≤ 5 * n := Nat.div_mul_le_self _ _
  have h4 : 5 * n < q * Ubot + Ubot := Nat.lt_div_mul_add hU
  constructor
  · calc Ubot * 2 ^ Tn n ≤ Ubot * q := Nat.mul_le_mul_left _ h1
      _ = q * Ubot := by ring
      _ ≤ 5 * n := h3
  · have : q + 1 ≤ 2 ^ (Tn n + 1) := h2
    calc 5 * n < q * Ubot + Ubot := h4
      _ = (q + 1) * Ubot := by ring
      _ ≤ 2 ^ (Tn n + 1) * Ubot := Nat.mul_le_mul_right _ this
      _ = 2 * Ubot * 2 ^ Tn n := by ring


/-! ### Numerical helpers -/

lemma c₁_le : c₁ ≤ 16 := by
  unfold c₁ C₀
  have h2 := Real.log_two_gt_d9
  have h4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
  rw [h4, div_le_iff₀ (by linarith)]
  nlinarith

lemma log_le_of_taylor {R c : ℝ} (hR : 0 < R) (hc : 0 ≤ c)
    (h : R ≤ ∑ i ∈ range 12, c ^ i / (i.factorial : ℝ)) : Real.log R ≤ c := by
  rw [Real.log_le_iff_le_exp hR]
  exact h.trans (Real.sum_le_exp_of_nonneg hc 12)

lemma sum_recip_nonneg (B : Finset ℕ) : 0 ≤ ∑ ℓ ∈ B, recip ℓ :=
  Finset.sum_nonneg fun ℓ _ => by unfold recip; positivity

/-- `Σ_{ℓ∈B} 1/ℓ ≤ log(a/b) + (a/b - 1)/256 + 1/1000` for a block `(2^{nb}, 2^{na}]`. -/
lemma sigma_custom_le (B : Finset ℕ) (n a b : ℕ) (hn : 2 ^ 23 ≤ n) (hb : 5 ≤ b) (hab : b ≤ a)
    (ha : a ≤ 4 * b) (hB : ∀ ℓ ∈ B, ℓ.Prime ∧ 2 ^ (n * b) < ℓ ∧ ℓ ≤ 2 ^ (n * a)) :
    ∑ ℓ ∈ B, recip ℓ ≤ Real.log ((a : ℝ) / b) + ((a : ℝ) / b - 1) / 256 + 1 / 1000 := by
  have hlo : 512 ≤ n * b := by nlinarith
  have h := sigma_interval_le B (fun ℓ h => (hB ℓ h).1) (n * b) (n * a) hlo
    (Nat.mul_le_mul_left _ hab) fun ℓ h => (hB ℓ h).2
  have hnR : (2 : ℝ) ^ 23 ≤ n := by exact_mod_cast hn
  have hbR : (5 : ℝ) ≤ b := by exact_mod_cast hb
  have habR : (b : ℝ) ≤ a := by exact_mod_cast hab
  have haR : (a : ℝ) ≤ 4 * b := by exact_mod_cast ha
  have hn0 : (0 : ℝ) < n := by linarith
  have hb0 : (0 : ℝ) < b := by linarith
  push_cast at h
  have e1 : Real.log ((n : ℝ) * a) - Real.log ((n : ℝ) * b) = Real.log ((a : ℝ) / b) := by
    have ha0 : (0 : ℝ) < a := by linarith
    rw [← Real.log_div (mul_pos hn0 ha0).ne' (mul_pos hn0 hb0).ne']
    congr 1; field_simp
  have e2 : ((n : ℝ) * a - n * b) / (256 * (n * b)) = ((a : ℝ) / b - 1) / 256 := by
    field_simp
  have e3 : c₁ * (512 * ((n : ℝ) * a - n * b) / (n * b) + 1) / (n * b) ≤ 1 / 1000 := by
    have hq : 512 * ((n : ℝ) * a - n * b) / (n * b) = 512 * ((a : ℝ) / b - 1) := by
      field_simp
    rw [hq]
    have hr : (a : ℝ) / b - 1 ≤ 3 := by
      rw [div_sub_one hb0.ne', div_le_iff₀ hb0]; linarith
    have hr0 : 0 ≤ (a : ℝ) / b - 1 := by
      rw [div_sub_one hb0.ne']; exact div_nonneg (by linarith) hb0.le
    have hc := c₁_le
    have hc0 := c₁_pos
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    have : (5 * 2 ^ 23 : ℝ) ≤ n * b := by nlinarith
    nlinarith
  linarith

/-- The ratio of a custom block. -/
lemma ratio_custom_le (B : Finset ℕ) (k n a b : ℕ) (hn : 2 ^ 23 ≤ n) (hb : 5 ≤ b) (hab : b ≤ a)
    (ha : a ≤ 4 * b) (hB : ∀ ℓ ∈ B, ℓ.Prime ∧ 2 ^ (n * b) < ℓ ∧ ℓ ≤ 2 ^ (n * a)) (c : ℝ)
    (hc : Real.log ((a : ℝ) / b) ≤ c)
    (hc2 : c + ((a : ℝ) / b - 1) / 256 + 1 / 1000 ≤ 2)
    (hε : ((a : ℝ) / b - 1) / 256 + 1 / 1000 + 1 / 10 ^ 6 < 1) :
    Eb (B, k) recip / Ub (B, k) recip ≤
      (c + (((a : ℝ) / b - 1) / 256 + 1 / 1000)) ^ (2 * k + 1) / (2 * k + 1).factorial *
        ((a : ℝ) / b) / (1 - (((a : ℝ) / b - 1) / 256 + 1 / 1000) - 1 / 10 ^ 6) := by
  set ε := ((a : ℝ) / b - 1) / 256 + 1 / 1000 with hεdef
  set σ := ∑ ℓ ∈ B, recip ℓ with hσ
  have hlo : 2 ≤ n * b := by nlinarith
  have h1 := ratio_le_of_sigma B k (n * b) hlo fun ℓ h => ⟨(hB ℓ h).1, (hB ℓ h).2.1⟩
  have hs := sigma_custom_le B n a b hn hb hab ha hB
  rw [← hσ] at h1 hs
  have hσ0 : 0 ≤ σ := sum_recip_nonneg B
  have hb0 : (0 : ℝ) < b := by exact_mod_cast (show 0 < b by omega)
  have hab' : (0 : ℝ) < (a : ℝ) / b := by
    have : (0 : ℝ) < a := by exact_mod_cast (show 0 < a by omega)
    positivity
  have hε0 : 0 ≤ ε := by
    rw [hεdef]
    have : (1 : ℝ) ≤ (a : ℝ) / b := by
      rw [le_div_iff₀ hb0]; simpa using (show (b : ℝ) ≤ a by exact_mod_cast hab)
    linarith
  have hσs : σ ≤ c + ε := by linarith
  have hσ2 : σ ≤ 2 := by linarith
  set η : ℝ := 1 / 2 ^ (n * b) with hη
  have hη0 : 0 ≤ η := by positivity
  have hη1 : 2 * η ≤ 1 / 10 ^ 6 := by
    rw [hη]
    have : (2 : ℝ) * 10 ^ 6 ≤ 2 ^ (n * b) := by
      calc (2 : ℝ) * 10 ^ 6 ≤ 2 ^ 21 := by norm_num
        _ ≤ 2 ^ (n * b) := pow_le_pow_right₀ (by norm_num) (by nlinarith)
    rw [mul_one_div, div_le_div_iff₀ (by positivity) (by positivity)]
    linarith
  have hexp : Real.exp ((1 + η) * σ) ≤ (a : ℝ) / b / (1 - ε - 1 / 10 ^ 6) := by
    have hx : (1 + η) * σ ≤ Real.log ((a : ℝ) / b) + (ε + 2 * η) := by nlinarith
    have hx0 : 0 ≤ ε + 2 * η := by positivity
    have hx1 : ε + 2 * η < 1 := by linarith
    calc Real.exp ((1 + η) * σ) ≤ Real.exp (Real.log ((a : ℝ) / b) + (ε + 2 * η)) :=
          Real.exp_le_exp.mpr hx
      _ = (a : ℝ) / b * Real.exp (ε + 2 * η) := by rw [Real.exp_add, Real.exp_log hab']
      _ ≤ (a : ℝ) / b * (1 / (1 - (ε + 2 * η))) :=
          mul_le_mul_of_nonneg_left (Real.exp_bound_div_one_sub_of_interval hx0 hx1) hab'.le
      _ ≤ (a : ℝ) / b * (1 / (1 - ε - 1 / 10 ^ 6)) := by
          apply mul_le_mul_of_nonneg_left _ hab'.le
          apply one_div_le_one_div_of_le (by linarith) (by linarith)
      _ = _ := by ring
  have hpow : σ ^ (2 * k + 1) ≤ (c + ε) ^ (2 * k + 1) := pow_le_pow_left₀ hσ0 hσs _
  have hf : (0 : ℝ) < (2 * k + 1).factorial := by exact_mod_cast Nat.factorial_pos _
  refine h1.trans ?_
  calc σ ^ (2 * k + 1) / ((2 * k + 1).factorial) * Real.exp ((1 + η) * σ)
      ≤ (c + ε) ^ (2 * k + 1) / ((2 * k + 1).factorial) * ((a : ℝ) / b / (1 - ε - 1 / 10 ^ 6)) := by
        apply mul_le_mul (div_le_div_of_nonneg_right hpow hf.le) hexp (Real.exp_pos _).le
        have : 0 ≤ c + ε := hσ0.trans hσs
        positivity
    _ = _ := by ring

/-- `Σ 1/ℓ ≤ 18/25` over a halving block `(2^{lo}, 2^{hi}]`, `hi ≤ 2 lo + 1`, `lo ≥ 2^{20}`. -/
lemma sigma_tail_le (B : Finset ℕ) (lo hi : ℕ) (hlo : Ubot ≤ lo) (hlh : lo ≤ hi)
    (hhi : hi ≤ 2 * lo + 1) (hB : ∀ ℓ ∈ B, ℓ.Prime ∧ 2 ^ lo < ℓ ∧ ℓ ≤ 2 ^ hi) :
    ∑ ℓ ∈ B, recip ℓ ≤ 18 / 25 := by
  have hlo' : 512 ≤ lo := by rw [Ubot_def] at hlo; omega
  have h := sigma_interval_le B (fun ℓ h => (hB ℓ h).1) lo hi hlo' hlh fun ℓ h => (hB ℓ h).2
  have hloR : (2 : ℝ) ^ 20 ≤ lo := by rw [Ubot_def] at hlo; exact_mod_cast hlo
  have hlhR : (lo : ℝ) ≤ hi := by exact_mod_cast hlh
  have hhiR : (hi : ℝ) ≤ 2 * lo + 1 := by exact_mod_cast hhi
  have hl0 : (0 : ℝ) < lo := by linarith
  have e1 : Real.log hi - Real.log lo ≤ Real.log 2 + 1 / (2 * lo) := by
    rw [← Real.log_div (ne_of_gt (by linarith)) hl0.ne']
    have h2 : (hi : ℝ) / lo = 2 * ((hi : ℝ) / (2 * lo)) := by field_simp
    have hpos : (0 : ℝ) < (hi : ℝ) / (2 * lo) := div_pos (by linarith) (by positivity)
    rw [h2, Real.log_mul (by norm_num) hpos.ne']
    have := Real.log_le_sub_one_of_pos hpos
    have : (hi : ℝ) / (2 * lo) - 1 ≤ 1 / (2 * lo) := by
      rw [div_sub_one (by positivity), div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith
    linarith
  have e2 : ((hi : ℝ) - lo) / (256 * lo) ≤ 1 / 256 + 1 / (256 * lo) := by
    have : ((hi : ℝ) - lo) ≤ lo + 1 := by linarith
    calc ((hi : ℝ) - lo) / (256 * lo) ≤ ((lo : ℝ) + 1) / (256 * lo) := by gcongr
      _ = _ := by field_simp
  have e3 : c₁ * (512 * ((hi : ℝ) - lo) / lo + 1) / lo ≤ 16 * 515 / lo := by
    have hc := c₁_le
    have hc0 := c₁_pos
    apply div_le_div_of_nonneg_right _ hl0.le
    have : 512 * ((hi : ℝ) - lo) / lo ≤ 514 := by
      rw [div_le_iff₀ hl0]; nlinarith
    have h0 : 0 ≤ 512 * ((hi : ℝ) - lo) / lo := by
      apply div_nonneg _ hl0.le; linarith
    nlinarith
  have hl2 := Real.log_two_lt_d9
  have e4 : 1 / (2 * (lo : ℝ)) + 1 / (256 * lo) + 16 * 515 / lo ≤ (16 * 515 + 1) / 2 ^ 20 := by
    rw [show 1 / (2 * (lo : ℝ)) + 1 / (256 * lo) + 16 * 515 / lo =
      (1 / 2 + 1 / 256 + 16 * 515) / lo by ring]
    rw [div_le_div_iff₀ hl0 (by norm_num)]
    nlinarith
  have : (16 * 515 + 1 : ℝ) / 2 ^ 20 ≤ 1 / 100 := by norm_num
  norm_num at hl2
  linarith

lemma ratio_tail_le (B : Finset ℕ) (k lo hi : ℕ) (hlo : Ubot ≤ lo) (hlh : lo ≤ hi)
    (hhi : hi ≤ 2 * lo + 1) (hB : ∀ ℓ ∈ B, ℓ.Prime ∧ 2 ^ lo < ℓ ∧ ℓ ≤ 2 ^ hi) :
    Eb (B, k) recip / Ub (B, k) recip ≤ (18 / 25 : ℝ) ^ (2 * k + 1) / (2 * k + 1).factorial * 4 := by
  have hlo2 : 2 ≤ lo := by rw [Ubot_def] at hlo; omega
  have h1 := ratio_le_of_sigma B k lo hlo2 fun ℓ h => ⟨(hB ℓ h).1, (hB ℓ h).2.1⟩
  have hs := sigma_tail_le B lo hi hlo hlh hhi hB
  have hσ0 := sum_recip_nonneg B
  set σ := ∑ ℓ ∈ B, recip ℓ
  have hη : (1 : ℝ) / 2 ^ lo ≤ 1 / 100 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    have : (100 : ℝ) ≤ 2 ^ lo :=
      calc (100 : ℝ) ≤ 2 ^ 7 := by norm_num
        _ ≤ 2 ^ lo := pow_le_pow_right₀ (by norm_num) (by rw [Ubot_def] at hlo; omega)
    linarith
  have hexp : Real.exp ((1 + 1 / 2 ^ lo) * σ) ≤ 4 := by
    have hx : (1 + 1 / 2 ^ lo) * σ ≤ 73 / 100 := by
      have : (0 : ℝ) ≤ 1 / 2 ^ lo := by positivity
      nlinarith
    calc Real.exp ((1 + 1 / 2 ^ lo) * σ) ≤ Real.exp (73 / 100) := Real.exp_le_exp.mpr hx
      _ ≤ 1 / (1 - 73 / 100) := Real.exp_bound_div_one_sub_of_interval (by norm_num) (by norm_num)
      _ ≤ 4 := by norm_num
  have hf : (0 : ℝ) < (2 * k + 1).factorial := by exact_mod_cast Nat.factorial_pos _
  refine h1.trans ?_
  apply mul_le_mul (div_le_div_of_nonneg_right (pow_le_pow_left₀ hσ0 hs _) hf.le) hexp
    (Real.exp_pos _).le (by positivity)

lemma tail_sum_le (T : ℕ) :
    ∑ i ∈ range T, (18 / 25 : ℝ) ^ (2 * (i + 3) + 1) / (2 * (i + 3) + 1).factorial * 4 ≤
      1 / 5000 := by
  have hterm : ∀ i, (18 / 25 : ℝ) ^ (2 * (i + 3) + 1) / (2 * (i + 3) + 1).factorial * 4 ≤
      ((18 / 25 : ℝ) ^ 7 / 5040 * 4) * (13 / 25) ^ i := by
    intro i
    have hf : (5040 : ℝ) ≤ (2 * (i + 3) + 1).factorial := by
      have := Nat.factorial_le (show 7 ≤ 2 * (i + 3) + 1 by omega)
      have h7 : (Nat.factorial 7 : ℝ) = 5040 := by norm_num [Nat.factorial]
      rw [← h7]; exact_mod_cast this
    have hp : (18 / 25 : ℝ) ^ (2 * (i + 3) + 1) = (18 / 25) ^ 7 * ((18 / 25) ^ 2) ^ i := by
      rw [← pow_mul, ← pow_add]; congr 1; omega
    have hq : ((18 / 25 : ℝ) ^ 2) ^ i ≤ (13 / 25) ^ i :=
      pow_le_pow_left₀ (by positivity) (by norm_num) i
    rw [hp]
    have h0 : (0 : ℝ) ≤ (18 / 25) ^ 7 * ((18 / 25) ^ 2) ^ i := by positivity
    calc (18 / 25 : ℝ) ^ 7 * ((18 / 25) ^ 2) ^ i / ((2 * (i + 3) + 1).factorial) * 4
        ≤ (18 / 25 : ℝ) ^ 7 * ((18 / 25) ^ 2) ^ i / 5040 * 4 := by
          gcongr
      _ ≤ (18 / 25 : ℝ) ^ 7 * (13 / 25) ^ i / 5040 * 4 := by gcongr
      _ = _ := by ring
  calc _ ≤ ∑ i ∈ range T, ((18 / 25 : ℝ) ^ 7 / 5040 * 4) * (13 / 25) ^ i :=
        Finset.sum_le_sum fun i _ => hterm i
    _ = ((18 / 25 : ℝ) ^ 7 / 5040 * 4) * ∑ i ∈ range T, (13 / 25 : ℝ) ^ i := by rw [Finset.mul_sum]
    _ ≤ ((18 / 25 : ℝ) ^ 7 / 5040 * 4) * (25 / 12) := by
        gcongr
        have h := geom_sum_mul (13 / 25 : ℝ) T
        have : (0 : ℝ) ≤ (13 / 25) ^ T := by positivity
        nlinarith
    _ ≤ 1 / 5000 := by norm_num


/-! ### The ratio sum -/

section Ratio

variable (P : Finset ℕ) (hP : ∀ ℓ ∈ P, ℓ.Prime)

include hP in
lemma ratio_custom_sum (n : ℕ) (hn : 2 ^ 23 ≤ n) :
    ∑ i ∈ range 5, Eb (midT P (eT n) levT i) recip / Ub (midT P (eT n) levT i) recip ≤
      ((7037 / 10000 : ℝ) + ((97 / 48 : ℝ) - 1) / 256 + 1 / 1000) ^ 3 / 6 * (97 / 48 : ℝ) / (1 - (((97 / 48 : ℝ) - 1) / 256 + 1 / 1000) - 1 / 10 ^ 6) +
      ((5535 / 10000 : ℝ) + ((40 / 23 : ℝ) - 1) / 256 + 1 / 1000) ^ 3 / 6 * (40 / 23 : ℝ) / (1 - (((40 / 23 : ℝ) - 1) / 256 + 1 / 1000) - 1 / 10 ^ 6) +
      ((10773 / 10000 : ℝ) + ((138 / 47 : ℝ) - 1) / 256 + 1 / 1000) ^ 5 / 120 * (138 / 47 : ℝ) / (1 - (((138 / 47 : ℝ) - 1) / 256 + 1 / 1000) - 1 / 10 ^ 6) +
      ((9059 / 10000 : ℝ) + ((47 / 19 : ℝ) - 1) / 256 + 1 / 1000) ^ 5 / 120 * (47 / 19 : ℝ) / (1 - (((47 / 19 : ℝ) - 1) / 256 + 1 / 1000) - 1 / 10 ^ 6) +
      ((13352 / 10000 : ℝ) + ((19 / 5 : ℝ) - 1) / 256 + 1 / 1000) ^ 7 / 5040 * (19 / 5 : ℝ) / (1 - (((19 / 5 : ℝ) - 1) / 256 + 1 / 1000) - 1 / 10 ^ 6) := by
  have key : ∀ (i a b k : ℕ) (c : ℝ), 5 ≤ b → b ≤ a → a ≤ 4 * b →
      eT n i = n * a → eT n (i + 1) = n * b → levT i = k →
      Real.log ((a : ℝ) / b) ≤ c → c + ((a : ℝ) / b - 1) / 256 + 1 / 1000 ≤ 2 →
      ((a : ℝ) / b - 1) / 256 + 1 / 1000 + 1 / 10 ^ 6 < 1 →
      Eb (midT P (eT n) levT i) recip / Ub (midT P (eT n) levT i) recip ≤
        (c + (((a : ℝ) / b - 1) / 256 + 1 / 1000)) ^ (2 * k + 1) / (2 * k + 1).factorial *
          ((a : ℝ) / b) / (1 - (((a : ℝ) / b - 1) / 256 + 1 / 1000) - 1 / 10 ^ 6) := by
    intro i a b k c hb hab ha hea heb hk hc hc2 hε
    have hB : ∀ ℓ ∈ (midT P (eT n) levT i).1, ℓ.Prime ∧ 2 ^ (n * b) < ℓ ∧ ℓ ≤ 2 ^ (n * a) := by
      intro ℓ h
      simp only [midT, Finset.mem_filter] at h
      rw [hea, heb] at h
      exact ⟨hP ℓ h.1, h.2⟩
    have := ratio_custom_le (midT P (eT n) levT i).1 k n a b hn hb hab ha
      hB c hc hc2 hε
    have h2 : (midT P (eT n) levT i).2 = k := by simp [midT, hk]
    have hpair : midT P (eT n) levT i = ((midT P (eT n) levT i).1, k) := Prod.ext rfl h2
    rw [hpair]
    exact this
  have h0 := key 0 485 240 1 (7037 / 10000) (by norm_num) (by norm_num) (by norm_num)
    (by simp [eT, ks]) (by simp [eT, ks]) (by simp [levT, kc])
    (by
      have e : (((485 : ℕ) : ℝ) / ((240 : ℕ) : ℝ)) = (97 / 48 : ℝ) := by norm_num
      rw [e]; refine log_le_of_taylor (by norm_num) (by norm_num) ?_
      norm_num [Finset.sum_range_succ, Nat.factorial])
    (by norm_num) (by norm_num)
  norm_num at h0
  have h1 := key 1 240 138 1 (5535 / 10000) (by norm_num) (by norm_num) (by norm_num)
    (by simp [eT, ks]) (by simp [eT, ks]) (by simp [levT, kc])
    (by
      have e : (((240 : ℕ) : ℝ) / ((138 : ℕ) : ℝ)) = (40 / 23 : ℝ) := by norm_num
      rw [e]; refine log_le_of_taylor (by norm_num) (by norm_num) ?_
      norm_num [Finset.sum_range_succ, Nat.factorial])
    (by norm_num) (by norm_num)
  norm_num at h1
  have h2 := key 2 138 47 2 (10773 / 10000) (by norm_num) (by norm_num) (by norm_num)
    (by simp [eT, ks]) (by simp [eT, ks]) (by simp [levT, kc])
    (by
      have e : (((138 : ℕ) : ℝ) / ((47 : ℕ) : ℝ)) = (138 / 47 : ℝ) := by norm_num
      rw [e]; refine log_le_of_taylor (by norm_num) (by norm_num) ?_
      norm_num [Finset.sum_range_succ, Nat.factorial])
    (by norm_num) (by norm_num)
  norm_num at h2
  have h3 := key 3 47 19 2 (9059 / 10000) (by norm_num) (by norm_num) (by norm_num)
    (by simp [eT, ks]) (by simp [eT, ks]) (by simp [levT, kc])
    (by
      have e : (((47 : ℕ) : ℝ) / ((19 : ℕ) : ℝ)) = (47 / 19 : ℝ) := by norm_num
      rw [e]; refine log_le_of_taylor (by norm_num) (by norm_num) ?_
      norm_num [Finset.sum_range_succ, Nat.factorial])
    (by norm_num) (by norm_num)
  norm_num at h3
  have h4 := key 4 19 5 3 (13352 / 10000) (by norm_num) (by norm_num) (by norm_num)
    (by simp [eT, ks]) (by simp [eT, ks]) (by simp [levT, kc])
    (by
      have e : (((19 : ℕ) : ℝ) / ((5 : ℕ) : ℝ)) = (19 / 5 : ℝ) := by norm_num
      rw [e]; refine log_le_of_taylor (by norm_num) (by norm_num) ?_
      norm_num [Finset.sum_range_succ, Nat.factorial])
    (by norm_num) (by norm_num)
  norm_num at h4
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  norm_num
  linarith

include hP in
lemma sigma_top_le (n : ℕ) (hn : 2 ^ 23 ≤ n) (hcard : 1000 * P.card ≤ 2 ^ (1000 * n)) :
    ∑ ℓ ∈ (topT P (eT n)).1, recip ℓ ≤
      7238 / 10000 + ((200 / 97 : ℝ) - 1) / 256 + 1 / 1000 + 1 / 1000 := by
  have he0 : eT n 0 = n * 485 := by simp [eT, ks]
  simp only [topT, he0]
  rw [← Finset.sum_filter_add_sum_filter_not (P.filter fun ℓ => 2 ^ (n * 485) < ℓ)
    (fun ℓ => ℓ ≤ 2 ^ (n * 1000))]
  have h1 := sigma_custom_le ((P.filter fun ℓ => 2 ^ (n * 485) < ℓ).filter
    fun ℓ => ℓ ≤ 2 ^ (n * 1000)) n 1000 485 hn (by norm_num) (by norm_num) (by norm_num)
    (fun ℓ h => by
      simp only [Finset.mem_filter] at h
      exact ⟨hP ℓ h.1.1, h.1.2, h.2⟩)
  have hlog : Real.log (((1000 : ℕ) : ℝ) / ((485 : ℕ) : ℝ)) ≤ 7238 / 10000 := by
    have e : (((1000 : ℕ) : ℝ) / ((485 : ℕ) : ℝ)) = (200 / 97 : ℝ) := by norm_num
    rw [e]; refine log_le_of_taylor (by norm_num) (by norm_num) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  have e2 : (((1000 : ℕ) : ℝ) / ((485 : ℕ) : ℝ)) = (200 / 97 : ℝ) := by norm_num
  rw [e2] at h1 hlog
  have h2 : ∑ ℓ ∈ (P.filter fun ℓ => 2 ^ (n * 485) < ℓ).filter (fun ℓ => ¬ ℓ ≤ 2 ^ (n * 1000)),
      recip ℓ ≤ 1 / 1000 := by
    set S := (P.filter fun ℓ => 2 ^ (n * 485) < ℓ).filter (fun ℓ => ¬ ℓ ≤ 2 ^ (n * 1000))
    have hpow : (0 : ℝ) < 2 ^ (1000 * n) := by positivity
    calc ∑ ℓ ∈ S, recip ℓ ≤ ∑ _ℓ ∈ S, (1 : ℝ) / 2 ^ (1000 * n) := by
          refine Finset.sum_le_sum fun ℓ h => ?_
          simp only [S, Finset.mem_filter, not_le] at h
          have : (2 : ℝ) ^ (1000 * n) < ℓ := by
            rw [mul_comm]; exact_mod_cast h.2
          exact one_div_le_one_div_of_le hpow this.le
      _ = S.card / 2 ^ (1000 * n) := by rw [Finset.sum_const, nsmul_eq_mul]; ring
      _ ≤ P.card / 2 ^ (1000 * n) := by
          gcongr
          exact (Finset.filter_subset (fun ℓ => ¬ ℓ ≤ 2 ^ (n * 1000)) _).trans
            (Finset.filter_subset (fun ℓ => 2 ^ (n * 485) < ℓ) P)
      _ ≤ 1 / 1000 := by
          rw [div_le_div_iff₀ hpow (by norm_num)]
          have : ((1000 * P.card : ℕ) : ℝ) ≤ ((2 ^ (1000 * n) : ℕ) : ℝ) := by exact_mod_cast hcard
          push_cast at this
          linarith
  linarith

include hP in
lemma ratio_tail_sum (n : ℕ) (hn : 2 ^ 23 ≤ n) :
    ∑ i ∈ range (Tn n), Eb (midT P (eT n) levT (5 + i)) recip /
      Ub (midT P (eT n) levT (5 + i)) recip ≤ 1 / 5000 := by
  refine le_trans (Finset.sum_le_sum fun i hi => ?_) (tail_sum_le (Tn n))
  have hiT := Finset.mem_range.mp hi
  obtain ⟨hT1, _⟩ := Tn_facts n hn
  set lo := 5 * n / 2 ^ (i + 1)
  set hi' := 5 * n / 2 ^ i
  have hlo : Ubot ≤ lo := by
    have h1 : 5 * n / 2 ^ Tn n ≤ lo :=
      Nat.div_le_div_left (Nat.pow_le_pow_right (by norm_num) (by omega)) (by positivity)
    have h2 : Ubot ≤ 5 * n / 2 ^ Tn n := (Nat.le_div_iff_mul_le (by positivity)).mpr hT1
    omega
  have hlo2 : lo = hi' / 2 := by
    simp only [lo, hi', pow_succ, Nat.div_div_eq_div_mul]
  have hlh : lo ≤ hi' := by rw [hlo2]; exact Nat.div_le_self _ _
  have hhi : hi' ≤ 2 * lo + 1 := by rw [hlo2]; omega
  have hB : ∀ ℓ ∈ (midT P (eT n) levT (5 + i)).1, ℓ.Prime ∧ 2 ^ lo < ℓ ∧ ℓ ≤ 2 ^ hi' := by
    intro ℓ h
    simp only [midT, Finset.mem_filter] at h
    rw [show 5 + i + 1 = 5 + (i + 1) by ring, eT_tail, eT_tail] at h
    exact ⟨hP ℓ h.1, h.2⟩
  have hlev : levT (5 + i) = i + 3 := by simp [levT]; omega
  have hpair : midT P (eT n) levT (5 + i) = ((midT P (eT n) levT (5 + i)).1, i + 3) :=
    Prod.ext rfl (by simp [midT, hlev])
  rw [hpair]
  exact ratio_tail_le _ (i + 3) lo hi' hlo hlh hhi hB

include hP in
theorem ratioSumU_bsT_le (n : ℕ) (hn : 2 ^ 23 ≤ n) (hcard : 1000 * P.card ≤ 2 ^ (1000 * n)) :
    ratioSumU (bsT P n) recip ≤ 24 / 25 := by
  simp only [bsT, blocksT, ratioSumU]
  have hbot : Eb (botT P (eT n) (Kn n) kbot) recip / Ub (botT P (eT n) (Kn n) kbot) recip = 0 := by
    obtain ⟨_, hT2⟩ := Tn_facts n hn
    have hK : eT n (Kn n) < 2 * Ubot := by
      rw [Kn, eT_tail]
      exact (Nat.div_lt_iff_lt_mul (by positivity)).mpr (by linarith)
    have hcard' : (botT P (eT n) (Kn n) kbot).1.card < 2 * kbot + 1 := by
      have hsub : (botT P (eT n) (Kn n) kbot).1 ⊆ Finset.Icc 1 (2 ^ eT n (Kn n)) := by
        intro ℓ h
        simp only [botT, Finset.mem_filter] at h
        exact Finset.mem_Icc.mpr ⟨(hP ℓ h.1).one_lt.le, h.2⟩
      have := Finset.card_le_card hsub
      rw [Nat.card_Icc] at this
      have : 2 ^ eT n (Kn n) ≤ 2 ^ (2 * Ubot) := Nat.pow_le_pow_right (by norm_num) hK.le
      have hk : kbot = 2 ^ (2 * Ubot) := rfl
      omega
    have hpair : botT P (eT n) (Kn n) kbot = ((botT P (eT n) (Kn n) kbot).1, kbot) := rfl
    rw [hpair]
    exact ratio_exact _ kbot hcard'
  rw [ratioSumU_map_range, hbot, show range (Kn n) = range (5 + Tn n) from rfl,
    Finset.sum_range_add]
  have hc := ratio_custom_sum P hP n hn
  have ht := ratio_tail_sum P hP n hn
  have htop' : Eb (topT P (eT n)) recip / Ub (topT P (eT n)) recip ≤
      7238 / 10000 + ((200 / 97 : ℝ) - 1) / 256 + 1 / 1000 + 1 / 1000 := by
    have hpair : topT P (eT n) = ((topT P (eT n)).1, 0) := rfl
    rw [hpair, ratio_topT]; exact sigma_top_le P hP n hn hcard
  have hnum : (7238 / 10000 + ((200 / 97 : ℝ) - 1) / 256 + 1 / 1000 + 1 / 1000) +
      (((7037 / 10000 : ℝ) + ((97 / 48 : ℝ) - 1) / 256 + 1 / 1000) ^ 3 / 6 * (97 / 48 : ℝ) / (1 - (((97 / 48 : ℝ) - 1) / 256 + 1 / 1000) - 1 / 10 ^ 6) +
      ((5535 / 10000 : ℝ) + ((40 / 23 : ℝ) - 1) / 256 + 1 / 1000) ^ 3 / 6 * (40 / 23 : ℝ) / (1 - (((40 / 23 : ℝ) - 1) / 256 + 1 / 1000) - 1 / 10 ^ 6) +
      ((10773 / 10000 : ℝ) + ((138 / 47 : ℝ) - 1) / 256 + 1 / 1000) ^ 5 / 120 * (138 / 47 : ℝ) / (1 - (((138 / 47 : ℝ) - 1) / 256 + 1 / 1000) - 1 / 10 ^ 6) +
      ((9059 / 10000 : ℝ) + ((47 / 19 : ℝ) - 1) / 256 + 1 / 1000) ^ 5 / 120 * (47 / 19 : ℝ) / (1 - (((47 / 19 : ℝ) - 1) / 256 + 1 / 1000) - 1 / 10 ^ 6) +
      ((13352 / 10000 : ℝ) + ((19 / 5 : ℝ) - 1) / 256 + 1 / 1000) ^ 7 / 5040 * (19 / 5 : ℝ) / (1 - (((19 / 5 : ℝ) - 1) / 256 + 1 / 1000) - 1 / 10 ^ 6))
      + 1 / 5000 ≤ 24 / 25 := by norm_num
  linarith

end Ratio


/-! ### The mass -/

lemma cardSum_eq_card (bs : List Block) (hd : Disj bs) : cardSum bs = (supp bs).card := by
  induction bs with
  | nil => simp [cardSum, supp]
  | cons b bs ih =>
    simp only [cardSum, supp]
    rw [Finset.card_union_of_disjoint hd.1, ih hd.2]

lemma massU_map_range (g : ℕ → Block) (t : ℕ) :
    massU ((List.range t).map g) = ∏ i ∈ range t, ((g i).1.card + 1 : ℝ) ^ (2 * (g i).2) := by
  induction t with
  | zero => simp [massU]
  | succ t ih =>
    rw [List.range_succ, List.map_append, Finset.prod_range_succ, ← ih]
    generalize (List.range t).map g = L
    induction L with
    | nil => simp [massU]
    | cons b L ih2 => simp only [List.cons_append, massU, ih2]; ring

lemma tail_weight_sum (T : ℕ) :
    ∑ i ∈ range T, (2 * (i : ℝ) + 6) / 2 ^ i = 16 - (4 * T + 16) / 2 ^ T := by
  induction T with
  | zero => norm_num
  | succ T ih =>
    rw [Finset.sum_range_succ, ih]
    push_cast
    field_simp
    ring

lemma tail_count_sum (T : ℕ) : ∑ i ∈ range T, (2 * (i : ℝ) + 6) ≤ 6 * 2 ^ T := by
  induction T with
  | zero => norm_num
  | succ T ih =>
    rw [Finset.sum_range_succ, pow_succ]
    have : (T : ℝ) + 1 ≤ 2 ^ T := by
      have := Nat.lt_two_pow_self (n := T)
      have : ((T + 1 : ℕ) : ℝ) ≤ ((2 ^ T : ℕ) : ℝ) := by exact_mod_cast this
      push_cast at this; linarith
    linarith

/-- The exponent sum of the middle blocks: `≤ 2385 n + 18`. -/
lemma mid_exponent_le (n : ℕ) (hn : 2 ^ 23 ≤ n) :
    ∑ i ∈ range (Kn n), (eT n i + 1) * (2 * levT i) ≤ 2385 * n + 18 := by
  rw [show Kn n = 5 + Tn n from rfl, Finset.sum_range_add]
  have h5 : ∑ i ∈ range 5, (eT n i + 1) * (2 * levT i) = 2304 * n + 18 := by
    simp [Finset.sum_range_succ, eT, ks, levT, kc]; ring
  rw [h5]
  have htail : ∑ i ∈ range (Tn n), (eT n (5 + i) + 1) * (2 * levT (5 + i)) ≤ 81 * n := by
    have hrw : ∀ i, (eT n (5 + i) + 1) * (2 * levT (5 + i)) = (5 * n / 2 ^ i + 1) * (2 * i + 6) := by
      intro i; rw [eT_tail]; congr 1; simp [levT]; omega
    simp_rw [hrw]
    obtain ⟨hT1, _⟩ := Tn_facts n hn
    have hR : ((∑ i ∈ range (Tn n), (5 * n / 2 ^ i + 1) * (2 * i + 6) : ℕ) : ℝ) ≤ 81 * n := by
      push_cast
      have hterm : ∀ i ∈ range (Tn n), (((5 * n / 2 ^ i : ℕ) : ℝ) + 1) * (2 * (i : ℝ) + 6) ≤
          5 * n * ((2 * (i : ℝ) + 6) / 2 ^ i) + (2 * (i : ℝ) + 6) := by
        intro i _
        have : ((5 * n / 2 ^ i : ℕ) : ℝ) ≤ (5 * n : ℝ) / 2 ^ i := by
          have := Nat.cast_div_le (α := ℝ) (m := 5 * n) (n := 2 ^ i)
          push_cast at this; exact this
        have h6 : (0 : ℝ) ≤ 2 * (i : ℝ) + 6 := by positivity
        calc (((5 * n / 2 ^ i : ℕ) : ℝ) + 1) * (2 * (i : ℝ) + 6)
            ≤ ((5 * n : ℝ) / 2 ^ i + 1) * (2 * (i : ℝ) + 6) := by gcongr
          _ = _ := by ring
      refine (Finset.sum_le_sum hterm).trans ?_
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, tail_weight_sum]
      have h1 := tail_count_sum (Tn n)
      have h2 : (0 : ℝ) ≤ (4 * (Tn n : ℝ) + 16) / 2 ^ Tn n := by positivity
      have h3 : 6 * (2 : ℝ) ^ Tn n ≤ n := by
        rw [Ubot_def] at hT1
        have : ((2 ^ 20 * 2 ^ Tn n : ℕ) : ℝ) ≤ ((5 * n : ℕ) : ℝ) := by exact_mod_cast hT1
        push_cast at this
        norm_num at this
        have : (0 : ℝ) ≤ 2 ^ Tn n := by positivity
        linarith
      have hn0 : (0 : ℝ) ≤ n := by positivity
      nlinarith
    exact_mod_cast hR
  omega

lemma card_filter_le_pow (P : Finset ℕ) (hP : ∀ ℓ ∈ P, ℓ.Prime) (e : ℕ) (f : ℕ → Prop)
    [DecidablePred f] (hf : ∀ ℓ, f ℓ → ℓ ≤ 2 ^ e) : (P.filter f).card ≤ 2 ^ e := by
  have hsub : P.filter f ⊆ Finset.Icc 1 (2 ^ e) := by
    intro ℓ h
    obtain ⟨h1, h2⟩ := Finset.mem_filter.mp h
    exact Finset.mem_Icc.mpr ⟨(hP ℓ h1).one_lt.le, hf ℓ h2⟩
  have := Finset.card_le_card hsub
  rwa [Nat.card_Icc, Nat.add_sub_cancel] at this

/-- The bottom-block constant. -/
noncomputable def Cbot : ℝ := ((2 : ℝ) ^ (2 * Ubot) + 1) ^ (2 * kbot)

lemma massU_bsT_le (P : Finset ℕ) (hP : ∀ ℓ ∈ P, ℓ.Prime) (n : ℕ) (hn : 2 ^ 23 ≤ n) :
    massU (bsT P n) ≤ Cbot * 2 ^ (2385 * n + 18) := by
  simp only [bsT, blocksT, massU]
  rw [massU_map_range]
  have htop : ((topT P (eT n)).1.card + 1 : ℝ) ^ (2 * (topT P (eT n)).2) = 1 := by
    simp [topT]
  have hbot : ((botT P (eT n) (Kn n) kbot).1.card + 1 : ℝ) ^ (2 * (botT P (eT n) (Kn n) kbot).2)
      ≤ Cbot := by
    obtain ⟨_, hT2⟩ := Tn_facts n hn
    have hK : eT n (Kn n) ≤ 2 * Ubot := by
      rw [Kn, eT_tail]
      exact ((Nat.div_lt_iff_lt_mul (by positivity)).mpr (by linarith)).le
    have hc : (botT P (eT n) (Kn n) kbot).1.card ≤ 2 ^ (2 * Ubot) :=
      (card_filter_le_pow P hP _ _ fun ℓ h => h).trans (Nat.pow_le_pow_right (by norm_num) hK)
    have hcR : ((botT P (eT n) (Kn n) kbot).1.card : ℝ) ≤ 2 ^ (2 * Ubot) := by exact_mod_cast hc
    unfold Cbot
    simp only [botT] at hcR ⊢
    gcongr
  have hmid : ∏ i ∈ range (Kn n), ((midT P (eT n) levT i).1.card + 1 : ℝ) ^
      (2 * (midT P (eT n) levT i).2) ≤ 2 ^ (2385 * n + 18) := by
    calc ∏ i ∈ range (Kn n), ((midT P (eT n) levT i).1.card + 1 : ℝ) ^
          (2 * (midT P (eT n) levT i).2)
        ≤ ∏ i ∈ range (Kn n), (2 : ℝ) ^ ((eT n i + 1) * (2 * levT i)) := by
          refine Finset.prod_le_prod₀ (fun i _ => by positivity) fun i _ => ?_
          have hc : (midT P (eT n) levT i).1.card ≤ 2 ^ eT n i :=
            card_filter_le_pow P hP _ _ fun ℓ h => h.2
          have hcR : ((midT P (eT n) levT i).1.card + 1 : ℝ) ≤ 2 ^ (eT n i + 1) := by
            have : ((midT P (eT n) levT i).1.card : ℝ) ≤ 2 ^ eT n i := by exact_mod_cast hc
            have : (1 : ℝ) ≤ 2 ^ eT n i := one_le_pow₀ (by norm_num)
            rw [pow_succ]; linarith
          rw [show (2 : ℝ) ^ ((eT n i + 1) * (2 * levT i)) = (2 ^ (eT n i + 1)) ^ (2 * levT i)
            from pow_mul _ _ _]
          exact pow_le_pow_left₀ (by positivity) hcR _
      _ = (2 : ℝ) ^ (∑ i ∈ range (Kn n), (eT n i + 1) * (2 * levT i)) :=
          Finset.prod_pow_eq_pow_sum _ _ _
      _ ≤ 2 ^ (2385 * n + 18) := pow_le_pow_right₀ (by norm_num) (mid_exponent_le n hn)
  rw [htop, one_mul]
  have h0 : (0 : ℝ) ≤ ∏ i ∈ range (Kn n), ((midT P (eT n) levT i).1.card + 1 : ℝ) ^
      (2 * (midT P (eT n) levT i).2) := Finset.prod_nonneg fun i _ => by positivity
  have hC0 : 0 ≤ Cbot := by unfold Cbot; positivity
  exact mul_le_mul hbot hmid h0 hC0

lemma one_le_massU (bs : List Block) : 1 ≤ massU bs := by
  induction bs with
  | nil => simp [massU]
  | cons b bs ih =>
    simp only [massU]
    have : (1 : ℝ) ≤ (b.1.card + 1 : ℝ) ^ (2 * b.2) :=
      one_le_pow₀ (by linarith [Nat.cast_nonneg (α := ℝ) b.1.card])
    nlinarith


/-! ### The product `∏ (1 - 1/ℓ)` -/

lemma exp_four_thirds_le : Real.exp (4 / 3) ≤ 9 := by
  have h := Real.exp_bound_div_one_sub_of_interval (x := 2 / 3) (by norm_num) (by norm_num)
  have : Real.exp (4 / 3) = Real.exp (2 / 3) ^ 2 := by
    rw [← Real.exp_nat_mul]; norm_num
  rw [this]
  have h0 := (Real.exp_pos (2 / 3)).le
  have : Real.exp (2 / 3) ≤ 3 := by norm_num at h; linarith
  nlinarith

lemma prod_P_ge (P : Finset ℕ) (hP : ∀ ℓ ∈ P, ℓ.Prime) (n : ℕ) (hn : 2 ^ 23 ≤ n)
    (hcard : 1000 * P.card ≤ 2 ^ (1000 * n)) :
    1 ≤ (∏ ℓ ∈ P, (1 - recip ℓ)) * (9 * ((2 : ℝ) ^ Ubot + 1) * 2 ^ n) := by
  classical
  rw [← Finset.prod_filter_mul_prod_filter_not P (fun ℓ => ℓ ≤ 2 ^ Ubot)]
  set Ps := P.filter fun ℓ => ℓ ≤ 2 ^ Ubot
  set Pb := P.filter fun ℓ => ¬ ℓ ≤ 2 ^ Ubot
  -- small primes
  have hs : 1 / ((2 : ℝ) ^ Ubot + 1) ≤ ∏ ℓ ∈ Ps, (1 - recip ℓ) := by
    have h := prod_one_sub_inv_ge Ps fun ℓ h => (hP ℓ (Finset.mem_filter.mp h).1).two_le
    have hc : Ps.card ≤ 2 ^ Ubot := card_filter_le_pow P hP Ubot _ fun ℓ h => h
    have hcR : (Ps.card : ℝ) ≤ 2 ^ Ubot := by exact_mod_cast hc
    have h' : 1 / ((Ps.card : ℝ) + 1) ≤ ∏ ℓ ∈ Ps, (1 - recip ℓ) := by simpa [recip] using h
    exact (one_div_le_one_div_of_le (by positivity) (by linarith)).trans h'
  -- large primes
  set σ := ∑ ℓ ∈ Pb, recip ℓ with hσ
  have hU3 : (1 : ℝ) / 3 ≤ 1 / 3 := le_rfl
  have hyb : ∀ ℓ ∈ Pb, 0 ≤ recip ℓ ∧ recip ℓ ≤ 1 / 3 := by
    intro ℓ h
    have h2 := (Finset.mem_filter.mp h).2
    push Not at h2
    have : (2 : ℝ) ^ Ubot < ℓ := by exact_mod_cast h2
    have h4 : (4 : ℝ) ≤ 2 ^ Ubot := by
      calc (4 : ℝ) = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ Ubot := pow_le_pow_right₀ (by norm_num) (by rw [Ubot_def]; norm_num)
    refine ⟨by unfold recip; positivity, ?_⟩
    unfold recip
    rw [div_le_div_iff₀ (by linarith) (by norm_num)]; linarith
  have hb := exp_le_prod' Pb recip (η := 1 / 3) le_rfl hyb
  rw [← hσ] at hb
  -- `σ ≤ 1000 n / 2^20 + 1`
  have hσle : σ ≤ 1000 * n / 2 ^ 20 + 1 := by
    rw [hσ, ← Finset.sum_filter_add_sum_filter_not Pb (fun ℓ => ℓ ≤ 2 ^ (1000 * n))]
    have hU : 1 ≤ Ubot := by rw [Ubot_def]; norm_num
    have hUn : Ubot ≤ 1000 * n := by rw [Ubot_def]; omega
    have h1 := sum_inv_shell_le'' (Pb.filter fun ℓ => ℓ ≤ 2 ^ (1000 * n))
      (fun ℓ h => hP ℓ (Finset.mem_filter.mp (Finset.mem_filter.mp h).1).1) Ubot (1000 * n) hU hUn
      (fun ℓ h => by
        have h' := Finset.mem_filter.mp h
        have h'' := (Finset.mem_filter.mp h'.1).2
        push Not at h''
        exact ⟨h'', h'.2⟩)
    have h2 : ∑ ℓ ∈ Pb.filter (fun ℓ => ¬ ℓ ≤ 2 ^ (1000 * n)), recip ℓ ≤ 1 / 1000 := by
      set S := Pb.filter (fun ℓ => ¬ ℓ ≤ 2 ^ (1000 * n))
      have hpow : (0 : ℝ) < 2 ^ (1000 * n) := by positivity
      calc ∑ ℓ ∈ S, recip ℓ ≤ ∑ _ℓ ∈ S, (1 : ℝ) / 2 ^ (1000 * n) := by
            refine Finset.sum_le_sum fun ℓ h => ?_
            have h' := (Finset.mem_filter.mp h).2
            push Not at h'
            have : (2 : ℝ) ^ (1000 * n) < ℓ := by exact_mod_cast h'
            exact one_div_le_one_div_of_le hpow this.le
        _ = S.card / 2 ^ (1000 * n) := by rw [Finset.sum_const, nsmul_eq_mul]; ring
        _ ≤ P.card / 2 ^ (1000 * n) := by
            gcongr
            exact (Finset.filter_subset _ _).trans (Finset.filter_subset _ _)
        _ ≤ 1 / 1000 := by
            rw [div_le_div_iff₀ hpow (by norm_num)]
            have : ((1000 * P.card : ℕ) : ℝ) ≤ ((2 ^ (1000 * n) : ℕ) : ℝ) := by exact_mod_cast hcard
            push_cast at this
            linarith
    simp only [recip] at h2 ⊢
    have hc := c₁_le
    rw [Ubot_def] at h1
    push_cast at h1
    have hn0 : (0 : ℝ) ≤ n := by positivity
    have : ((1000 * n : ℝ) - 2 ^ 20) / 2 ^ 20 + c₁ / 2 ^ 20 ≤ 1000 * n / 2 ^ 20 + 1 / 2 := by
      rw [← add_div, div_le_iff₀ (by positivity)]
      have : (1000 * n / 2 ^ 20 + 1 / 2 : ℝ) * 2 ^ 20 = 1000 * n + 2 ^ 19 := by ring
      rw [this]; linarith
    linarith
  -- `exp((4/3) σ) ≤ 9 · 2^n`
  have hexp : Real.exp ((1 + 1 / 3) * σ) ≤ 9 * 2 ^ n := by
    have h1 : (1 + 1 / 3) * σ ≤ n * Real.log 2 + 4 / 3 := by
      have hl2 := Real.log_two_gt_d9
      have hn0 : (0 : ℝ) ≤ n := by positivity
      nlinarith
    calc Real.exp ((1 + 1 / 3) * σ) ≤ Real.exp (n * Real.log 2 + 4 / 3) := Real.exp_le_exp.mpr h1
      _ = 2 ^ n * Real.exp (4 / 3) := by
          rw [Real.exp_add, Real.exp_nat_mul, Real.exp_log (by norm_num)]
      _ ≤ 2 ^ n * 9 := mul_le_mul_of_nonneg_left exp_four_thirds_le (by positivity)
      _ = 9 * 2 ^ n := by ring
  have hinv : Real.exp ((1 + 1 / 3) * σ) * Real.exp (-((1 + 1 / 3) * σ)) = 1 := by
    rw [← Real.exp_add]; simp
  have hpos1 : (0 : ℝ) < 2 ^ Ubot + 1 := by positivity
  have hs' : 1 ≤ (∏ ℓ ∈ Ps, (1 - recip ℓ)) * ((2 : ℝ) ^ Ubot + 1) := by
    rw [div_le_iff₀ hpos1] at hs; linarith
  have hb' : 1 ≤ (∏ ℓ ∈ Pb, (1 - recip ℓ)) * (9 * 2 ^ n) := by
    have := mul_le_mul_of_nonneg_left hb (Real.exp_pos ((1 + 1 / 3) * σ)).le
    have h0 : 0 ≤ ∏ ℓ ∈ Pb, (1 - recip ℓ) := (Real.exp_pos _).le.trans hb
    nlinarith
  have hPs0 : 0 ≤ ∏ ℓ ∈ Ps, (1 - recip ℓ) := by
    have : (0 : ℝ) < 1 / ((2 : ℝ) ^ Ubot + 1) := by positivity
    linarith
  calc (1 : ℝ) ≤ ((∏ ℓ ∈ Ps, (1 - recip ℓ)) * ((2 : ℝ) ^ Ubot + 1)) *
        ((∏ ℓ ∈ Pb, (1 - recip ℓ)) * (9 * 2 ^ n)) := by nlinarith
    _ = _ := by ring


/-! ### The bound for large `ω(p - 1)` -/

irreducible_def E23 : ℕ := 1000 * 2 ^ 23

/-- The threshold `2^{1000 · 2^{23}}` on `ω(p - 1)`. -/
irreducible_def M0 : ℕ := 2 ^ E23

lemma one_le_M0 : 1 ≤ M0 := by rw [M0_def]; exact Nat.one_le_two_pow

/-- `2^{1000}`, kept opaque. -/
irreducible_def T1000 : ℕ := 2 ^ 1000

lemma T1000_pos : 0 < T1000 := by rw [T1000_def]; positivity

/-- `K₁ = Cbot · 2^{18} · 225 (2^U + 1)`. -/
noncomputable def K₁ : ℝ := Cbot * 2 ^ 18 * 225 * ((2 : ℝ) ^ Ubot + 1)

/-- The constant for large `ω`: `1089 · 4 K₁² (2^{1000} · 1000)^5`. -/
noncomputable def C7 : ℝ := 1089 * 4 * K₁ ^ 2 * ((T1000 : ℝ) * 1000) ^ 5

lemma K₁_pos : 0 < K₁ := by unfold K₁ Cbot; positivity

theorem le_of_no_primitive_root_lt_seven (hGRH : DirichletLNonvanishingRightOfHalf)
    (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (x : ℕ) (hx1 : 1 ≤ x) (hxp : x ≤ p)
    (hno : ∀ g : ℕ, 0 < g → g < x → orderOf (g : ZMod p) ≠ p - 1)
    (hm : M0 ≤ (p - 1).primeFactors.card) :
    (x : ℝ) ≤ C7 * ((p - 1).primeFactors.card : ℝ) ^ 7 * Real.log p ^ 2 := by
  classical
  set P := (p - 1).primeFactors with hPdef
  set m := P.card with hmdef
  have hP : ∀ ℓ ∈ P, ℓ.Prime := fun ℓ h => (Nat.mem_primeFactors.mp h).1
  have hm1 : 1 ≤ m := le_trans one_le_M0 hm
  -- choose `n`
  have hex : ∃ n, 1000 * m ≤ 2 ^ (1000 * n) := ⟨m + 1, by
    have h1 : m < 2 ^ m := Nat.lt_two_pow_self
    have h2 : 2 ^ (m + 10) ≤ 2 ^ (1000 * (m + 1)) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have : 2 ^ (m + 10) = 1024 * 2 ^ m := by rw [pow_add]; ring
    omega⟩
  set n := Nat.find hex with hndef
  have hcard : 1000 * m ≤ 2 ^ (1000 * n) := Nat.find_spec hex
  have hn : 2 ^ 23 ≤ n := by
    by_contra h
    push Not at h
    have h3 : 2 ^ (1000 * n) ≤ M0 := by
      rw [M0_def]; exact Nat.pow_le_pow_right (by norm_num) (by rw [E23_def]; omega)
    omega
  have hlt : 2 ^ (1000 * n) < T1000 * (1000 * m) := by
    have := Nat.find_min hex (show n - 1 < n by omega)
    push Not at this
    have e : 2 ^ (1000 * n) = T1000 * 2 ^ (1000 * (n - 1)) := by
      rw [T1000_def, ← pow_add]; congr 1; omega
    rw [e]
    exact Nat.mul_lt_mul_of_pos_left this T1000_pos
  -- the sieve
  set bs := bsT P n with hbs
  have hd : Disj bs := blocksT_disj P levT kbot (eT_anti n)
  have hsupp : supp bs = P := blocksT_supp P levT kbot
  have hR := ratioSumU_bsT_le P hP n hn hcard
  have hrep := (isRep_phi2 bs hd).2
  set M := (1 + cardSum bs : ℝ) * massU bs with hM
  have hM1 : 1 ≤ M := by
    have := one_le_massU bs
    have : (0 : ℝ) ≤ cardSum bs := Nat.cast_nonneg _
    rw [hM]; nlinarith
  have hrec : ∀ ℓ ∈ supp bs, 0 ≤ recip ℓ ∧ recip ℓ ≤ 1 / 2 := fun ℓ h =>
    recip_mem (hP ℓ (hsupp ▸ h))
  have hΦ := phi_ge_U recip bs hrec (by linarith)
  set θ := prodA bs recip * (1 / 25) with hθ
  have hprod : prodA bs recip = ∏ ℓ ∈ P, (1 - recip ℓ) := by rw [prodA_eq_prod hd, hsupp]
  have hpg := prod_P_ge P hP n hn hcard
  rw [← hprod] at hpg
  have hA0 : 0 < prodA bs recip := by
    by_contra h; push Not at h
    have : (0 : ℝ) ≤ 9 * ((2 : ℝ) ^ Ubot + 1) * 2 ^ n := by positivity
    nlinarith
  have hθpos : 0 < θ := by rw [hθ]; positivity
  have hθΦ : θ ≤ phi bs recip := by
    refine le_trans ?_ hΦ
    rw [hθ]; apply mul_le_mul_of_nonneg_left (by linarith) hA0.le
  have key := le_of_no_primitive_root_lt' hGRH p hp hp2 x hx1 hxp hno bs hsupp M θ hrep hM1
    hθpos hθΦ
  -- bound `M / θ`
  have hcs : (cardSum bs : ℝ) ≤ m := by
    rw [cardSum_eq_card bs hd, hsupp]
  have hmass := massU_bsT_le P hP n hn
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm1
  set L := Real.log p with hL
  have hL0 : 0 ≤ L := Real.log_nonneg (by exact_mod_cast hp.one_lt.le)
  have hC0 : 0 ≤ Cbot := by unfold Cbot; positivity
  have h1 : M ≤ 2 * m * (Cbot * 2 ^ (2385 * n + 18)) := by
    rw [hM]
    have : (1 + cardSum bs : ℝ) ≤ 2 * m := by linarith
    exact mul_le_mul this hmass (by linarith [one_le_massU bs]) (by positivity)
  have hinvθ : 1 / θ ≤ 225 * ((2 : ℝ) ^ Ubot + 1) * 2 ^ n := by
    rw [hθ, div_le_iff₀ (by positivity)]
    nlinarith
  have hMθ : M / θ ≤ 2 * m * K₁ * 2 ^ (2386 * n) := by
    rw [div_eq_mul_one_div]
    calc M * (1 / θ) ≤ 2 * m * (Cbot * 2 ^ (2385 * n + 18)) *
          (225 * ((2 : ℝ) ^ Ubot + 1) * 2 ^ n) :=
          mul_le_mul h1 hinvθ (by positivity) (by positivity)
      _ = 2 * m * K₁ * 2 ^ (2386 * n) := by
          rw [K₁, show 2386 * n = 2385 * n + n by ring, pow_add, pow_add]; ring
  have hMLθ : M * L / θ ≤ 2 * m * K₁ * 2 ^ (2386 * n) * L := by
    rw [mul_div_right_comm]
    exact mul_le_mul_of_nonneg_right hMθ hL0
  have h0 : 0 ≤ M * L / θ := by
    have : (0 : ℝ) ≤ M := by linarith
    positivity
  have hpow5 : (2 : ℝ) ^ (4772 * n) ≤ ((T1000 : ℝ) * 1000) ^ 5 * (m : ℝ) ^ 5 := by
    have h2 : ((2 ^ (1000 * n) : ℕ) : ℝ) ≤ ((T1000 * (1000 * m) : ℕ) : ℝ) := by
      exact_mod_cast hlt.le
    push_cast at h2
    calc (2 : ℝ) ^ (4772 * n) ≤ 2 ^ (5000 * n) := pow_le_pow_right₀ (by norm_num) (by omega)
      _ = ((2 : ℝ) ^ (1000 * n)) ^ 5 := by rw [← pow_mul]; ring_nf
      _ ≤ ((T1000 : ℝ) * (1000 * m)) ^ 5 := pow_le_pow_left₀ (by positivity) h2 5
      _ = ((T1000 : ℝ) * 1000) ^ 5 * (m : ℝ) ^ 5 := by ring
  calc (x : ℝ) ≤ 1089 * (M * L / θ) ^ 2 := key
    _ ≤ 1089 * (2 * m * K₁ * 2 ^ (2386 * n) * L) ^ 2 := by gcongr
    _ = 1089 * 4 * K₁ ^ 2 * (m : ℝ) ^ 2 * (2 : ℝ) ^ (4772 * n) * L ^ 2 := by
        rw [show 4772 * n = 2386 * n * 2 by ring, pow_mul]; ring
    _ ≤ 1089 * 4 * K₁ ^ 2 * (m : ℝ) ^ 2 * (((T1000 : ℝ) * 1000) ^ 5 * (m : ℝ) ^ 5) * L ^ 2 := by
        gcongr
    _ = C7 * (m : ℝ) ^ 7 * L ^ 2 := by rw [C7]; ring

end Shoup.Sieve

namespace Shoup

open Sieve ArithmeticFunction
open scoped ArithmeticFunction.omega

lemma HasPrimitiveRootLE.mono {p : ℕ} {B B' : ℝ} (h : HasPrimitiveRootLE p B) (hB : B ≤ B') :
    HasPrimitiveRootLE p B' := by
  obtain ⟨g, hg, hgB, hord⟩ := h
  exact ⟨g, hg, hgB.trans hB, hord⟩

/-- The constant of `PolyOmegaStatement 7`. -/
noncomputable def C7total : ℝ := C7 + polyC * (M0 : ℝ) ^ 129

/-- **Main theorem (exponent 7).** Under GRH, every odd prime `p` has a primitive root
`0 < g ≤ C ω(p-1)^7 (log p)²`. -/
theorem leastPrimitiveRoot_le_seven_of_GRH (hGRH : Erdos985.DirichletLNonvanishingRightOfHalf)
    (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) :
    HasPrimitiveRootLE p (C7total * (ω (p - 1) : ℝ) ^ 7 * Real.log p ^ 2) := by
  have hL : 0 ≤ Real.log p := Real.log_nonneg (by exact_mod_cast hp.one_lt.le)
  have hK := K₁_pos
  have hC7 : 0 ≤ C7 := by unfold C7; have := T1000_pos; positivity
  have hpC : 0 ≤ polyC := by rw [polyC_def]; have := c16_pos; positivity
  have hm : 1 ≤ ω (p - 1) := by
    rw [cardDistinctFactors_eq_card_primeFactors]; exact one_le_card_primeFactors p hp hp2
  have hmR : (1 : ℝ) ≤ ω (p - 1) := by exact_mod_cast hm
  by_cases hbig : M0 ≤ (p - 1).primeFactors.card
  · have h := hasPrimitiveRootLE_of_bound p hp (C7 * ((p - 1).primeFactors.card : ℝ) ^ 7 *
      Real.log p ^ 2) (by positivity) fun x hx1 hxp hno =>
        le_of_no_primitive_root_lt_seven hGRH p hp hp2 x hx1 hxp hno hbig
    rw [← cardDistinctFactors_eq_card_primeFactors] at h
    refine h.mono ?_
    have h0 : 0 ≤ polyC * (M0 : ℝ) ^ 129 := by positivity
    have h7 : 0 ≤ (ω (p - 1) : ℝ) ^ 7 * Real.log p ^ 2 := by positivity
    have hle : C7 ≤ C7total := by unfold C7total; linarith
    calc C7 * (ω (p - 1) : ℝ) ^ 7 * Real.log p ^ 2 = C7 * ((ω (p - 1) : ℝ) ^ 7 * Real.log p ^ 2) := by ring
      _ ≤ C7total * ((ω (p - 1) : ℝ) ^ 7 * Real.log p ^ 2) := mul_le_mul_of_nonneg_right hle h7
      _ = _ := by ring
  · push Not at hbig
    have h := leastPrimitiveRoot_le_poly_of_GRH hGRH p hp hp2
    refine h.mono ?_
    rw [← cardDistinctFactors_eq_card_primeFactors] at hbig
    have hmM : (ω (p - 1) : ℝ) ≤ M0 := by exact_mod_cast hbig.le
    have h129 : (ω (p - 1) : ℝ) ^ 129 ≤ (M0 : ℝ) ^ 129 :=
      pow_le_pow_left₀ (by positivity) hmM 129
    have hsplit : (ω (p - 1) : ℝ) ^ 136 = (ω (p - 1) : ℝ) ^ 129 * (ω (p - 1) : ℝ) ^ 7 := by
      rw [← pow_add]
    have h7 : 0 ≤ (ω (p - 1) : ℝ) ^ 7 * Real.log p ^ 2 := by positivity
    rw [hsplit]
    have hle : polyC * (M0 : ℝ) ^ 129 ≤ C7total := by unfold C7total; linarith
    calc polyC * ((ω (p - 1) : ℝ) ^ 129 * (ω (p - 1) : ℝ) ^ 7) * Real.log p ^ 2
        = polyC * (ω (p - 1) : ℝ) ^ 129 * ((ω (p - 1) : ℝ) ^ 7 * Real.log p ^ 2) := by ring
      _ ≤ polyC * (M0 : ℝ) ^ 129 * ((ω (p - 1) : ℝ) ^ 7 * Real.log p ^ 2) := by
          apply mul_le_mul_of_nonneg_right _ h7
          exact mul_le_mul_of_nonneg_left h129 hpC
      _ ≤ C7total * ((ω (p - 1) : ℝ) ^ 7 * Real.log p ^ 2) := mul_le_mul_of_nonneg_right hle h7
      _ = _ := by ring

/-- `PolyOmegaStatement 7` holds under GRH. -/
theorem polyOmega7_of_GRH (hGRH : Erdos985.DirichletLNonvanishingRightOfHalf) :
    PolyOmegaStatement 7 :=
  ⟨C7total, fun p hp hp2 => leastPrimitiveRoot_le_seven_of_GRH hGRH p hp hp2⟩

end Shoup
