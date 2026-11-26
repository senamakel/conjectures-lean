import Shoup.Rosser.Defs
import Shoup.Sieve.Factor

/-!
# Mertens' product over a logarithmic range

For a finite set `S` of primes `q > 2^{2^36}` with `z^{1/t} ≤ q < z` (`t ≥ 1`),

`∏_{q ∈ S} (1 - 1/q)⁻¹ ≤ Ω(t) = (1001/1000) · t · (1 + (t - 1)/1000)`.

This is Mertens' theorem `∏_{z^{1/t} ≤ q < z} (1 - 1/q)⁻¹ ≈ t` with explicit errors, from the
block bound `sigma_block_le` (`Shoup/Sieve/Factor.lean`) chained over ranges `(2^lo, 2^{4 lo}]`.
-/

namespace Shoup.Rosser

open Finset Shoup.Sieve

/-- The threshold exponent: every prime in the Rosser sieve exceeds `2^E`. -/
irreducible_def E : ℕ := 2 ^ 36

lemma E_ge : 36 ≤ E := by rw [E_def]; norm_num

/-- The Mertens majorant `Ω(t) = (1001/1000) t (1 + (t-1)/1000)`. -/
noncomputable def Om (t : ℝ) : ℝ := 1001 / 1000 * t * (1 + (t - 1) / 1000)

lemma one_le_Om {t : ℝ} (ht : 1 ≤ t) : 1 ≤ Om t := by
  unfold Om; nlinarith

lemma Om_mono {s t : ℝ} (hs : 1 ≤ s) (hst : s ≤ t) : Om s ≤ Om t := by
  unfold Om; nlinarith

lemma Om_le_sq {t : ℝ} (ht : 1 ≤ t) : Om t ≤ (1001 / 1000) ^ 2 * t ^ 2 := by
  unfold Om; nlinarith

/-- The per-block error `3/4096 + 10^{-5}`. -/
noncomputable def cσ : ℝ := 3 / 4096 + 1 / 10 ^ 5

lemma cσ_pos : 0 < cσ := by unfold cσ; norm_num

lemma log_four_gt : (1.386 : ℝ) < Real.log 4 := by
  have h := Real.log_two_gt_d9
  have : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
  rw [this]; linarith

/-- **Chained Mertens bound.** For primes in `(2^lo, 2^hi]`, `lo ≥ 2^36`:
`Σ 1/q ≤ (1 + cσ/log 4) log(hi/lo) + cσ`. -/
theorem sigma_chain (S : Finset ℕ) (hS : ∀ ℓ ∈ S, ℓ.Prime) : ∀ (n lo hi : ℕ), hi - lo ≤ n →
    2 ^ 36 ≤ lo → lo ≤ hi → (∀ ℓ ∈ S, 2 ^ lo < ℓ ∧ ℓ ≤ 2 ^ hi) →
    ∑ ℓ ∈ S, recip ℓ ≤ (1 + cσ / Real.log 4) * Real.log ((hi : ℝ) / lo) + cσ := by
  intro n
  induction n using Nat.strong_induction_on generalizing S with
  | _ n ih =>
  intro lo hi hn hlo hlh hrange
  have hl4 := log_four_gt
  have hloR : (2 : ℝ) ^ 36 ≤ lo := by exact_mod_cast hlo
  have hl0 : (0 : ℝ) < lo := by linarith [show (0 : ℝ) < 2 ^ 36 by positivity]
  have hlhR : (lo : ℝ) ≤ hi := by exact_mod_cast hlh
  have hlog0 : 0 ≤ Real.log ((hi : ℝ) / lo) :=
    Real.log_nonneg (by rw [le_div_iff₀ hl0]; linarith)
  have hc := cσ_pos
  have hcl : 0 ≤ cσ / Real.log 4 := by positivity
  by_cases h4 : hi ≤ 4 * lo
  · have h := sigma_block_le S hS lo hi hlo hlh h4 hrange
    have h4R : (hi : ℝ) ≤ 4 * lo := by exact_mod_cast h4
    have e : ((hi : ℝ) - lo) / (4096 * lo) ≤ 3 / 4096 := by
      rw [div_le_iff₀ (by positivity)]; nlinarith
    have : 0 ≤ cσ / Real.log 4 * Real.log ((hi : ℝ) / lo) := mul_nonneg hcl hlog0
    unfold cσ at *
    nlinarith
  · push Not at h4
    rw [← Finset.sum_filter_add_sum_filter_not S (fun ℓ => ℓ ≤ 2 ^ (4 * lo))]
    have h1 := sigma_block_le (S.filter fun ℓ => ℓ ≤ 2 ^ (4 * lo))
      (fun ℓ h => hS ℓ (Finset.mem_filter.mp h).1) lo (4 * lo) hlo (by omega) le_rfl
      (fun ℓ h => ⟨(hrange ℓ (Finset.mem_filter.mp h).1).1, (Finset.mem_filter.mp h).2⟩)
    have h2 := ih (hi - 4 * lo) (by omega) (S.filter fun ℓ => ¬ ℓ ≤ 2 ^ (4 * lo))
      (fun ℓ h => hS ℓ (Finset.mem_filter.mp h).1) (4 * lo) hi le_rfl (by omega) (by omega)
      (fun ℓ h => by
        obtain ⟨hm, hn'⟩ := Finset.mem_filter.mp h
        exact ⟨by omega, (hrange ℓ hm).2⟩)
    have e1 : ((4 * lo : ℕ) : ℝ) / lo = 4 := by push_cast; field_simp
    have e2 : Real.log ((hi : ℝ) / ((4 * lo : ℕ) : ℝ)) = Real.log ((hi : ℝ) / lo) - Real.log 4 := by
      push_cast
      rw [show (hi : ℝ) / (4 * lo) = (hi / lo) / 4 by field_simp]
      rw [Real.log_div (div_pos (by linarith) hl0).ne' (by norm_num)]
    have e3 : (((4 * lo : ℕ) : ℝ) - lo) / (4096 * lo) = 3 / 4096 := by push_cast; field_simp; ring
    rw [e1, e3] at h1
    rw [e2] at h2
    have hl4' : Real.log 4 ≠ 0 := by linarith
    have : cσ / Real.log 4 * Real.log 4 = cσ := by field_simp
    unfold cσ at *
    nlinarith

lemma one_div_sub_inv_le_exp {y : ℝ} (h0 : 0 ≤ y) (hy : y ≤ 1 / 2 ^ 36) :
    (1 - y)⁻¹ ≤ Real.exp ((1 + 1 / 2 ^ 36) * y) := by
  have h := one_sub_ge_exp (η := 1 / 2 ^ 36) h0 hy (by norm_num)
  have hpos : 0 < 1 - y := by
    have : (1 : ℝ) / 2 ^ 36 < 1 := by norm_num
    linarith
  rw [Real.exp_neg] at h
  rw [inv_le_comm₀ hpos (Real.exp_pos _)]
  exact h

lemma exp_le_Om {t a b : ℝ} (ht : 1 ≤ t) (ha1 : 0 ≤ a - 1) (ha2 : a - 1 ≤ 1 / 1000)
    (hb0 : 0 ≤ b) (hb1 : b ≤ 8 / 10000) : Real.exp (a * Real.log t + b) ≤ Om t := by
  have ht0 : 0 < t := by linarith
  have hsplit : Real.exp (a * Real.log t + b) =
      t * Real.exp ((a - 1) * Real.log t) * Real.exp b := by
    rw [← Real.exp_log ht0]
    rw [Real.log_exp, ← Real.exp_add, ← Real.exp_add]; congr 1; ring
  have hbern : Real.exp ((a - 1) * Real.log t) ≤ 1 + (a - 1) * (t - 1) := by
    have h := rpow_one_add_le_one_add_mul_self (s := t - 1) (by linarith) ha1
      (by linarith)
    rw [show 1 + (t - 1) = t by ring, Real.rpow_def_of_pos ht0, mul_comm] at h
    exact h
  have hexpb : Real.exp b ≤ 1 + b + b ^ 2 := by
    have h := Real.abs_exp_sub_one_sub_id_le (x := b) (by rw [abs_of_nonneg hb0]; linarith)
    have := (abs_le.mp h).2
    linarith
  calc Real.exp (a * Real.log t + b) = t * Real.exp ((a - 1) * Real.log t) * Real.exp b := hsplit
    _ ≤ t * (1 + (a - 1) * (t - 1)) * (1 + b + b ^ 2) := by
        apply mul_le_mul (mul_le_mul_of_nonneg_left hbern ht0.le) hexpb (Real.exp_pos _).le
        have : 0 ≤ (a - 1) * (t - 1) := mul_nonneg ha1 (by linarith)
        positivity
    _ ≤ Om t := by
        unfold Om
        have h0 : 0 ≤ t - 1 := by linarith
        have h1' : (a - 1) * (t - 1) ≤ 1 / 1000 * (t - 1) := mul_le_mul_of_nonneg_right ha2 h0
        have h1 : 1 + (a - 1) * (t - 1) ≤ 1 + (t - 1) / 1000 := by linarith
        have hbb : b ^ 2 ≤ (8 / 10000) ^ 2 := pow_le_pow_left₀ hb0 hb1 2
        have h2 : 1 + b + b ^ 2 ≤ 1001 / 1000 := by nlinarith
        have h3 : 0 ≤ 1 + (a - 1) * (t - 1) := by
          have := mul_nonneg ha1 h0; linarith
        calc t * (1 + (a - 1) * (t - 1)) * (1 + b + b ^ 2)
            ≤ t * (1 + (t - 1) / 1000) * (1001 / 1000) := by
              apply mul_le_mul (mul_le_mul_of_nonneg_left h1 ht0.le) h2 (by positivity)
              have : 0 ≤ (t - 1) / 1000 := by linarith
              positivity
          _ = 1001 / 1000 * t * (1 + (t - 1) / 1000) := by ring


/-- **Mertens' product.** -/
theorem prod_inv_le_Om (S : Finset ℕ) (z t : ℝ) (ht : 1 ≤ t)
    (hS : ∀ q ∈ S, q.Prime ∧ 2 ^ E < q ∧ (q : ℝ) < z ∧ Real.log z ≤ t * Real.log q) :
    ∏ q ∈ S, (1 - recip q)⁻¹ ≤ Om t := by
  rcases S.eq_empty_or_nonempty with hSe | ⟨q₀, hq₀⟩
  · rw [hSe, Finset.prod_empty]; exact one_le_Om ht
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hE : (2 : ℝ) ^ 36 ≤ (2 : ℝ) ^ E := pow_le_pow_right₀ (by norm_num) E_ge
  have h1E : (1 : ℝ) < 2 ^ E := one_lt_pow₀ (by norm_num) (by have := E_ge; omega)
  -- facts about each `q`
  have hq1 : ∀ q ∈ S, (2 : ℝ) ^ E < q := fun q h => by exact_mod_cast (hS q h).2.1
  have hqpos : ∀ q ∈ S, (0 : ℝ) < q := fun q h => lt_trans (by positivity) (hq1 q h)
  have hz : (0 : ℝ) < z := (hqpos q₀ hq₀).trans (hS q₀ hq₀).2.2.1
  set L2 := Real.log z / Real.log 2 with hL2
  set lo := max E (⌊L2 / t⌋₊ - 1) with hlo
  set hi := ⌈L2⌉₊ with hhi
  have hlogq : ∀ q ∈ S, L2 / t ≤ Real.log q / Real.log 2 := by
    intro q h
    rw [div_div, div_le_div_iff₀ (by positivity) hl2]
    have := (hS q h).2.2.2
    nlinarith
  have hlogE : ∀ q ∈ S, (E : ℝ) < Real.log q / Real.log 2 := by
    intro q h
    rw [lt_div_iff₀ hl2, ← Real.log_pow]
    exact Real.log_lt_log (by positivity) (hq1 q h)
  have hlo_lt : ∀ q ∈ S, (lo : ℝ) < Real.log q / Real.log 2 := by
    intro q h
    rw [hlo, Nat.cast_max]
    refine max_lt (hlogE q h) ?_
    set n := ⌊L2 / t⌋₊
    rcases Nat.eq_zero_or_pos n with hn | hn
    · rw [hn]; simp only [Nat.zero_sub, Nat.cast_zero]
      have : (0 : ℝ) < E := by exact_mod_cast (show 0 < E by have := E_ge; omega)
      exact lt_trans this (hlogE q h)
    · have hnn : 0 ≤ L2 / t := by
        by_contra hneg; push Not at hneg
        have : n = 0 := Nat.floor_eq_zero.mpr (by linarith)
        omega
      have hfl : (n : ℝ) ≤ L2 / t := Nat.floor_le hnn
      rw [Nat.cast_sub hn]; push_cast
      linarith [hlogq q h]
  have hrange : ∀ q ∈ S, 2 ^ lo < q ∧ q ≤ 2 ^ hi := by
    intro q h
    constructor
    · have : ((2 ^ lo : ℕ) : ℝ) < q := by
        push_cast
        rw [← Real.log_lt_log_iff (by positivity) (hqpos q h), Real.log_pow]
        have := hlo_lt q h
        rw [lt_div_iff₀ hl2] at this; linarith
      exact_mod_cast this
    · have : (q : ℝ) ≤ ((2 ^ hi : ℕ) : ℝ) := by
        push_cast
        refine ((hS q h).2.2.1).le.trans ?_
        rw [← Real.log_le_log_iff hz (by positivity), Real.log_pow]
        have : L2 ≤ (hi : ℝ) := Nat.le_ceil L2
        rw [hL2, div_le_iff₀ hl2] at this; linarith
      exact_mod_cast this
  have hloE : 2 ^ 36 ≤ lo := le_trans (by rw [E_def]) (le_max_left _ _)
  have hlh : lo ≤ hi := by
    obtain ⟨h1, h2⟩ := hrange q₀ hq₀
    have : 2 ^ lo < 2 ^ hi := lt_of_lt_of_le h1 h2
    exact ((Nat.pow_lt_pow_iff_right (by norm_num)).mp this).le
  have hσ := sigma_chain S (fun q h => (hS q h).1) (hi - lo) lo hi le_rfl hloE hlh hrange
  -- the ratio `hi / lo`
  have hloR : (2 : ℝ) ^ 36 ≤ lo := by exact_mod_cast hloE
  have hl0 : (0 : ℝ) < lo := lt_of_lt_of_le (by positivity) hloR
  have hL2nonneg : 0 ≤ L2 := by
    have := hlogq q₀ hq₀
    have h2 := hlogE q₀ hq₀
    have : (0 : ℝ) ≤ E := Nat.cast_nonneg _
    rw [hL2]
    apply div_nonneg _ hl2.le
    have : Real.log 1 < Real.log z := Real.log_lt_log (by norm_num)
      (lt_trans h1E ((hq1 q₀ hq₀).trans (hS q₀ hq₀).2.2.1))
    rw [Real.log_one] at this; linarith
  have hratio : (hi : ℝ) / lo ≤ t * (1 + 3 / 2 ^ 36) := by
    have hhiR : (hi : ℝ) < L2 + 1 := Nat.ceil_lt_add_one hL2nonneg
    have hfl : L2 / t < (⌊L2 / t⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one _
    have hsub : ((⌊L2 / t⌋₊ : ℕ) : ℝ) ≤ ((⌊L2 / t⌋₊ - 1 : ℕ) : ℝ) + 1 := by
      have : ⌊L2 / t⌋₊ ≤ ⌊L2 / t⌋₊ - 1 + 1 := by omega
      exact_mod_cast this
    have hmax : ((⌊L2 / t⌋₊ - 1 : ℕ) : ℝ) ≤ lo := by exact_mod_cast le_max_right _ _
    have h1 : L2 ≤ t * (lo + 2) := by
      have : L2 / t < lo + 2 := by linarith
      rw [div_lt_iff₀ (by linarith)] at this
      linarith
    rw [div_le_iff₀ hl0]
    have : 3 * t ≤ t * (3 / 2 ^ 36) * lo := by
      have : (3 / 2 ^ 36 : ℝ) * lo ≥ 3 := by
        rw [ge_iff_le, div_mul_eq_mul_div, le_div_iff₀ (by positivity)]; nlinarith
      nlinarith
    nlinarith
  have hratio1 : 1 ≤ (hi : ℝ) / lo := by
    rw [le_div_iff₀ hl0]; simpa using (show (lo : ℝ) ≤ hi by exact_mod_cast hlh)
  have hlogr : Real.log ((hi : ℝ) / lo) ≤ Real.log t + 3 / 2 ^ 36 := by
    have h := Real.log_le_log (by linarith) hratio
    rw [Real.log_mul (by linarith) (by positivity)] at h
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 1 + 3 / 2 ^ 36 by positivity)
    linarith
  -- the product
  have hprod : ∏ q ∈ S, (1 - recip q)⁻¹ ≤ Real.exp ((1 + 1 / 2 ^ 36) * ∑ q ∈ S, recip q) := by
    rw [Finset.mul_sum, Real.exp_sum]
    refine Finset.prod_le_prod₀ (fun q h => ?_) fun q h => ?_
    · have : recip q < 1 := by
        unfold recip; rw [div_lt_one (hqpos q h)]
        linarith [hq1 q h]
      exact inv_nonneg.mpr (by linarith)
    · apply one_div_sub_inv_le_exp (by unfold recip; exact (one_div_pos.mpr (hqpos q h)).le)
      unfold recip
      exact one_div_le_one_div_of_le (by positivity) ((hE).trans (hq1 q h).le)
  refine hprod.trans ?_
  -- `exp((1+η)(c₁ log t + b)) ≤ Ω(t)`
  have hl4 := log_four_gt
  have hc := cσ_pos
  have hc1 : cσ / Real.log 4 ≤ 6 / 10000 := by
    rw [div_le_iff₀ (by linarith)]; unfold cσ; nlinarith
  have hlt : 0 ≤ Real.log t := Real.log_nonneg ht
  set a := (1 + 1 / 2 ^ 36 : ℝ) * (1 + cσ / Real.log 4) with ha
  set b := (1 + 1 / 2 ^ 36 : ℝ) * ((1 + cσ / Real.log 4) * (3 / 2 ^ 36) + cσ) with hb
  have hσ' : (1 + 1 / 2 ^ 36) * ∑ q ∈ S, recip q ≤ a * Real.log t + b := by
    have : ∑ q ∈ S, recip q ≤ (1 + cσ / Real.log 4) * (Real.log t + 3 / 2 ^ 36) + cσ := by
      refine hσ.trans ?_
      have : 0 ≤ 1 + cσ / Real.log 4 := by positivity
      nlinarith
    rw [ha, hb]; nlinarith
  have hcl0 : 0 ≤ cσ / Real.log 4 := by positivity
  have ha1 : 0 ≤ a - 1 := by rw [ha]; nlinarith
  have ha2 : a - 1 ≤ 1 / 1000 := by rw [ha]; nlinarith
  have hb0 : 0 ≤ b := by rw [hb]; positivity
  have hb1 : b ≤ 8 / 10000 := by
    rw [hb]; unfold cσ at hc1 ⊢; nlinarith
  exact (Real.exp_le_exp.mpr hσ').trans (exp_le_Om ht ha1 ha2 hb0 hb1)

end Shoup.Rosser
