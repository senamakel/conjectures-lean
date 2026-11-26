import Shoup.Sieve.Buchstab
import Shoup.Sieve.Fixed

/-!
# One block of an upper Brun–Hooley sieve: the factor `U/A`

For a block `(B, k)` of primes and the weights `g = 1/ℓ`, the factor `U_b/A_b` of `ratProd` is

* `1` if `B = ∅` (`factor_empty`) or the block is exact, `|B| < 2k + 1` (`factor_exact`);
* `1/A ≤ exp((1+η)σ)` at level `k = 0` (`factor_zero_le`);
* `≤ 1 + σ^{2k+1}/(2k+1)! · exp((1+η)σ)` in general (`factor_le`),

where `σ = Σ_{ℓ∈B} 1/ℓ` and every `ℓ ∈ B` exceeds `2^lo`, `η = 2^{-lo}`.

`sigma_block_le` is Mertens for a block `(2^{lo}, 2^{hi}]`, `lo ≥ 2^{36}`, `hi ≤ 4 lo`:
`σ ≤ log(hi/lo) + (hi - lo)/(4096 lo) + 10^{-5}`. `factor_le_facN` turns all this into the
fixed-point bound `facN a b k c` for a block `(2^{bn}, 2^{an}]`.
-/

namespace Shoup.Sieve

open Finset Fixed

/-! ### The factor of one block -/

lemma factor_empty (k : ℕ) (y : ℕ → ℝ) : Ub ((∅ : Finset ℕ), k) y / Ab ((∅ : Finset ℕ), k) y = 1 := by
  simp [Ub, Ab, G_empty]

lemma factor_exact (B : Finset ℕ) (k : ℕ) (y : ℕ → ℝ) (hy : ∀ ℓ ∈ B, 0 ≤ y ℓ ∧ y ℓ ≤ 1 / 2)
    (hk : B.card < 2 * k + 1) : Ub (B, k) y / Ab (B, k) y = 1 := by
  have hy' : ∀ ℓ ∈ (B, k).1, 0 ≤ y ℓ ∧ y ℓ ≤ 1 := fun ℓ h => ⟨(hy ℓ h).1, by linarith [(hy ℓ h).2]⟩
  obtain ⟨_, aU, aL⟩ := block_bounds y (B, k) hy'
  have hE : Eb (B, k) y = 0 := by
    unfold Eb E
    rw [Finset.powersetCard_eq_empty.mpr hk]
    simp
  have hA := Ab_pos y (B, k) hy
  rw [hE, sub_zero] at aL
  rw [le_antisymm aL aU, div_self hA.ne']

lemma factor_zero_le (B : Finset ℕ) (y : ℕ → ℝ) {η : ℝ} (hη : η ≤ 1 / 3)
    (hy : ∀ ℓ ∈ B, 0 ≤ y ℓ ∧ y ℓ ≤ η) :
    Ub (B, 0) y / Ab (B, 0) y ≤ Real.exp ((1 + η) * ∑ ℓ ∈ B, y ℓ) := by
  have hP := exp_le_prod' B y hη hy
  have hpos : 0 < ∏ ℓ ∈ B, (1 - y ℓ) := (Real.exp_pos _).trans_le hP
  simp only [Ub, Ab, mul_zero, zero_add, G_one]
  rw [div_le_iff₀ hpos]
  have hinv : Real.exp ((1 + η) * ∑ ℓ ∈ B, y ℓ) * Real.exp (-((1 + η) * ∑ ℓ ∈ B, y ℓ)) = 1 := by
    rw [← Real.exp_add]; simp
  calc (1 : ℝ) = Real.exp ((1 + η) * ∑ ℓ ∈ B, y ℓ) * Real.exp (-((1 + η) * ∑ ℓ ∈ B, y ℓ)) :=
        hinv.symm
    _ ≤ _ := mul_le_mul_of_nonneg_left hP (Real.exp_pos _).le

lemma factor_le (B : Finset ℕ) (k : ℕ) (y : ℕ → ℝ) {η : ℝ} (hη : η ≤ 1 / 3)
    (hy : ∀ ℓ ∈ B, 0 ≤ y ℓ ∧ y ℓ ≤ η) :
    Ub (B, k) y / Ab (B, k) y ≤ 1 + (∑ ℓ ∈ B, y ℓ) ^ (2 * k + 1) / (2 * k + 1).factorial *
      Real.exp ((1 + η) * ∑ ℓ ∈ B, y ℓ) := by
  have hy2 : ∀ ℓ ∈ B, 0 ≤ y ℓ ∧ y ℓ ≤ 1 / 2 := fun ℓ h =>
    ⟨(hy ℓ h).1, (hy ℓ h).2.trans (by linarith)⟩
  have hy1 : ∀ ℓ ∈ (B, k).1, 0 ≤ y ℓ ∧ y ℓ ≤ 1 := fun ℓ h =>
    ⟨(hy2 ℓ h).1, by linarith [(hy2 ℓ h).2]⟩
  obtain ⟨_, _, aL⟩ := block_bounds y (B, k) hy1
  have hA := Ab_pos y (B, k) hy2
  have hE := E_div_prod_le' (2 * k + 1) B y hη hy
  have h1 : Ub (B, k) y / Ab (B, k) y ≤ 1 + Eb (B, k) y / Ab (B, k) y := by
    rw [div_le_iff₀ hA, add_mul, one_mul, div_mul_cancel₀ _ hA.ne']; linarith
  exact h1.trans (by simpa [Eb, Ab] using hE)

/-- Monotone form of `factor_le` in `σ`. -/
lemma factor_le_of_sigma (B : Finset ℕ) (k : ℕ) (y : ℕ → ℝ) {η σ : ℝ} (hη0 : 0 ≤ η)
    (hη : η ≤ 1 / 3) (hy : ∀ ℓ ∈ B, 0 ≤ y ℓ ∧ y ℓ ≤ η) (hσ : ∑ ℓ ∈ B, y ℓ ≤ σ) :
    Ub (B, k) y / Ab (B, k) y ≤
      (if k = 0 then Real.exp ((1 + η) * σ)
       else 1 + σ ^ (2 * k + 1) / (2 * k + 1).factorial * Real.exp ((1 + η) * σ)) := by
  have hs0 : 0 ≤ ∑ ℓ ∈ B, y ℓ := Finset.sum_nonneg fun ℓ h => (hy ℓ h).1
  have hexp : Real.exp ((1 + η) * ∑ ℓ ∈ B, y ℓ) ≤ Real.exp ((1 + η) * σ) :=
    Real.exp_le_exp.mpr (by nlinarith)
  split_ifs with hk
  · subst hk; exact (factor_zero_le B y hη hy).trans hexp
  · refine (factor_le B k y hη hy).trans ?_
    have hf : (0 : ℝ) < (2 * k + 1).factorial := by exact_mod_cast Nat.factorial_pos _
    have hp := pow_le_pow_left₀ hs0 hσ (2 * k + 1)
    have h1 := div_le_div_of_nonneg_right hp hf.le
    have hσ0 : 0 ≤ σ := hs0.trans hσ
    have h2 := mul_le_mul h1 hexp (Real.exp_pos _).le (by positivity)
    linarith

/-! ### Mertens for a block, shells of width `lo / 4096` -/

theorem sigma_block_le (S : Finset ℕ) (hS : ∀ ℓ ∈ S, ℓ.Prime) (lo hi : ℕ) (hlo : 2 ^ 36 ≤ lo)
    (hlh : lo ≤ hi) (hhi : hi ≤ 4 * lo) (hrange : ∀ ℓ ∈ S, 2 ^ lo < ℓ ∧ ℓ ≤ 2 ^ hi) :
    ∑ ℓ ∈ S, recip ℓ ≤ Real.log ((hi : ℝ) / lo) + ((hi : ℝ) - lo) / (4096 * lo) + 1 / 10 ^ 5 := by
  set w := lo / 4096 with hw
  have hw1 : 1 ≤ w := by rw [hw]; omega
  have h := sum_inv_blockM_le w hw1 (hi - lo) lo hi rfl S hS (by omega) hlh hrange
  have hloR : (2 : ℝ) ^ 36 ≤ lo := by exact_mod_cast hlo
  have hlhR : (lo : ℝ) ≤ hi := by exact_mod_cast hlh
  have hhiR : (hi : ℝ) ≤ 4 * lo := by exact_mod_cast hhi
  have hl0 : (0 : ℝ) < lo := by linarith
  have hwR : (w : ℝ) ≤ lo / 4096 := by
    rw [hw, le_div_iff₀ (by norm_num)]; exact_mod_cast Nat.div_mul_le_self lo 4096
  have hwR2 : (lo : ℝ) / 8192 ≤ w := by
    rw [hw, div_le_iff₀ (by norm_num)]
    have := Nat.lt_div_mul_add (a := lo) (show 0 < 4096 by norm_num)
    have : (lo : ℝ) < (lo / 4096 : ℕ) * 4096 + 4096 := by exact_mod_cast this
    have : (4096 : ℝ) ≤ (lo / 4096 : ℕ) * 4096 := by
      have : 1 ≤ lo / 4096 := by omega
      have : (1 : ℝ) ≤ (lo / 4096 : ℕ) := by exact_mod_cast this
      linarith
    linarith
  have hwpos : (0 : ℝ) < w := by exact_mod_cast hw1
  have hc := c₁_pos
  have hc16 := c₁_le
  have hd : (0 : ℝ) ≤ hi - lo := by linarith
  simp only [recip]
  refine h.trans ?_
  have e0 : Real.log hi - Real.log lo = Real.log ((hi : ℝ) / lo) := by
    rw [Real.log_div (ne_of_gt (by linarith)) hl0.ne']
  have e1 : (w : ℝ) * (hi - lo) / (lo : ℝ) ^ 2 ≤ ((hi : ℝ) - lo) / (4096 * lo) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have : (w : ℝ) * 4096 ≤ lo := by linarith
    nlinarith [mul_le_mul_of_nonneg_right this (mul_nonneg hd (by positivity : (0 : ℝ) ≤ lo))]
  have e2 : c₁ * (((hi : ℝ) - lo) / w + 1) / lo ≤ 1 / 10 ^ 5 := by
    have hq : ((hi : ℝ) - lo) / w ≤ 8192 * 3 := by
      rw [div_le_iff₀ hwpos]; nlinarith
    have hq0 : 0 ≤ ((hi : ℝ) - lo) / w := div_nonneg hd hwpos.le
    rw [div_le_div_iff₀ hl0 (by norm_num)]
    nlinarith
  linarith

/-! ### Fixed-point bounds for one block -/

lemma xq_ge (s : ℕ) : (1 + 1 / 10 ^ 6 : ℝ) * r s ≤ r (xq s) := by
  unfold xq
  refine le_trans (le_of_eq ?_) (cdiv_ge (s * (10 ^ 6 + 1)) (10 ^ 6) (by norm_num))
  unfold r; push_cast; ring

lemma sigq_ge (a b c : ℕ) (hb : 0 < b) (hab : b ≤ a) :
    r c + ((a : ℝ) - b) / (4096 * b) + 1 / 10 ^ 5 ≤ r (sigq a b c) := by
  have hD : (0 : ℝ) < Dn := by exact_mod_cast Dn_pos
  unfold sigq
  rw [r_add, r_add]
  have e1 : ((a : ℝ) - b) / (4096 * b) ≤ r (cdiv ((a - b) * Dn) (4096 * b)) := by
    refine le_trans (le_of_eq ?_) (cdiv_ge ((a - b) * Dn) (4096 * b) (by omega))
    unfold r; rw [Nat.cast_mul, Nat.cast_sub hab, Nat.cast_mul]; field_simp; norm_num
  have e2 : (1 : ℝ) / 10 ^ 5 ≤ r (cdiv Dn (10 ^ 5)) := by
    refine le_trans (le_of_eq ?_) (cdiv_ge Dn (10 ^ 5) (by norm_num))
    rw [r_Dn]; norm_num
  linarith

/-- **The factor of a block `(2^{bn}, 2^{an}]`** (any subset of its primes) is at most
`facN a b k c / D`. -/
theorem factor_le_facN {a b n : ℕ} (B : Finset ℕ) (hB : ∀ ℓ ∈ B, ℓ.Prime ∧ 2 ^ (b * n) < ℓ ∧ ℓ ≤ 2 ^ (a * n))
    (k c : ℕ) (hn : 2 ^ 36 ≤ n) (hok : rowOK a b k c = true) :
    Ub (B, k) recip / Ab (B, k) recip ≤ r (facN a b k c) := by
  simp only [rowOK, Bool.and_eq_true, decide_eq_true_eq] at hok
  obtain ⟨⟨⟨⟨hb, hab⟩, ha4⟩, hlog⟩, hx16⟩ := hok
  have hlo : 2 ^ 36 ≤ b * n := le_trans hn (Nat.le_mul_of_pos_left n hb)
  have hσ := sigma_block_le B (fun ℓ h => (hB ℓ h).1) (b * n) (a * n) hlo
    (Nat.mul_le_mul_right n hab.le) (by nlinarith) fun ℓ h => (hB ℓ h).2
  have hn0 : (0 : ℝ) < n := by
    have : (0 : ℝ) < 2 ^ 36 := by positivity
    exact this.trans_le (by exact_mod_cast hn)
  have hb0 : (0 : ℝ) < b := by exact_mod_cast hb
  have e1 : Real.log (((a * n : ℕ) : ℝ) / ((b * n : ℕ) : ℝ)) = Real.log ((a : ℝ) / b) := by
    push_cast; congr 1; field_simp
  have e2 : (((a * n : ℕ) : ℝ) - ((b * n : ℕ) : ℝ)) / (4096 * ((b * n : ℕ) : ℝ)) =
      ((a : ℝ) - b) / (4096 * b) := by push_cast; field_simp
  rw [e1, e2] at hσ
  have hl := log_le_of_lowSum (by omega) hb hlog
  have hsq := sigq_ge a b c hb hab.le
  set s := sigq a b c
  have hσs : ∑ ℓ ∈ B, recip ℓ ≤ r s := by linarith
  -- `η = 2^{-bn} ≤ 10^{-6}`
  set η : ℝ := 1 / 2 ^ (b * n) with hη
  have hη0 : 0 ≤ η := by positivity
  have hη6 : η ≤ 1 / 10 ^ 6 := by
    rw [hη, div_le_div_iff₀ (by positivity) (by positivity)]
    have : (10 : ℝ) ^ 6 ≤ 2 ^ (b * n) :=
      calc (10 : ℝ) ^ 6 ≤ 2 ^ 20 := by norm_num
        _ ≤ 2 ^ (b * n) := pow_le_pow_right₀ (by norm_num) (by omega)
    linarith
  have hy : ∀ ℓ ∈ B, 0 ≤ recip ℓ ∧ recip ℓ ≤ η := by
    intro ℓ h
    have : (2 : ℝ) ^ (b * n) < ℓ := by exact_mod_cast (hB ℓ h).2.1
    exact ⟨by unfold recip; positivity, one_div_le_one_div_of_le (by positivity) this.le⟩
  have hf := factor_le_of_sigma B k recip hη0 (by linarith) hy hσs
  have hs0 : 0 ≤ r s := r_nonneg s
  have hxs : (1 + η) * r s ≤ r (xq s) :=
    le_trans (by nlinarith) (xq_ge s)
  have hexp : Real.exp ((1 + η) * r s) ≤ r (expU (xq s)) := exp_le_expU_of hxs hx16
  refine hf.trans ?_
  unfold facN
  split_ifs with hk
  · exact hexp
  · rw [r_add, r_Dn]
    have hp := powU_ge s (2 * k + 1)
    have hc := cdiv_ge (powU s (2 * k + 1)) (2 * k + 1).factorial (Nat.factorial_pos _)
    have h1 : r s ^ (2 * k + 1) / ((2 * k + 1).factorial : ℝ) ≤
        r (cdiv (powU s (2 * k + 1)) (2 * k + 1).factorial) :=
      le_trans (div_le_div_of_nonneg_right hp (by positivity)) hc
    have := mulU_ge_of (by positivity) (Real.exp_pos _).le h1 hexp
    linarith

end Shoup.Sieve
