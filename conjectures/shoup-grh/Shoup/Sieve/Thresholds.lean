import Shoup.Poly
import Shoup.Sieve.BrunHooley2
import Shoup.Sieve.Mertens

/-!
# Block decompositions from a decreasing sequence of thresholds

For thresholds `e 0 ≥ e 1 ≥ … ≥ e K`, the blocks are
`top = {ℓ ∈ P : ℓ > 2^{e 0}}` (level 1), `mid i = {ℓ ∈ P : 2^{e(i+1)} < ℓ ≤ 2^{e i}}` (level
`2 lev i + 1`, `i < K`) and `bot = {ℓ ∈ P : ℓ ≤ 2^{e K}}` (level `2 kbot + 1`). They partition `P`.

Per block: `Σ_{ℓ∈mid} 1/ℓ` is bounded by Mertens (`sigma_mid_le`), and the Brun–Hooley ratio
`e/U` by Maclaurin (`ratio_le_of_sigma`).
-/

namespace Shoup.Sieve

open Finset

section Blocks

variable (P : Finset ℕ) (e lev : ℕ → ℕ) (K kbot : ℕ)

def topT : Block := (P.filter fun ℓ => 2 ^ e 0 < ℓ, 0)
def botT : Block := (P.filter fun ℓ => ℓ ≤ 2 ^ e K, kbot)
def midT (i : ℕ) : Block := (P.filter fun ℓ => 2 ^ e (i + 1) < ℓ ∧ ℓ ≤ 2 ^ e i, lev i)

def blocksT : List Block := topT P e :: botT P e K kbot :: (List.range K).map (midT P e lev)

variable {e K}

lemma e_anti (he : ∀ i < K, e (i + 1) ≤ e i) {i j : ℕ} (hij : i ≤ j) (hj : j ≤ K) : e j ≤ e i := by
  induction j, hij using Nat.le_induction with
  | base => exact le_rfl
  | succ j hij ih => exact (he j (by omega)).trans (ih (by omega))

lemma pow_e_anti (he : ∀ i < K, e (i + 1) ≤ e i) {i j : ℕ} (hij : i ≤ j) (hj : j ≤ K) :
    2 ^ e j ≤ 2 ^ e i := Nat.pow_le_pow_right (by norm_num) (e_anti he hij hj)

lemma blocksT_disj (he : ∀ i < K, e (i + 1) ≤ e i) : Disj (blocksT P e lev K kbot) := by
  apply disj_of_pairwise
  refine List.Pairwise.cons ?_ (List.Pairwise.cons ?_ ?_)
  · intro c hc
    rcases List.mem_cons.mp hc with rfl | hc
    · refine Finset.disjoint_left.mpr fun ℓ h1 h2 => ?_
      simp only [topT, botT, Finset.mem_filter] at h1 h2
      have := pow_e_anti he (Nat.zero_le K) le_rfl
      omega
    · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hc
      have hi := List.mem_range.mp hi
      have := pow_e_anti he (Nat.zero_le i) (by omega)
      refine Finset.disjoint_left.mpr fun ℓ h1 h2 => ?_
      simp only [topT, midT, Finset.mem_filter] at h1 h2
      omega
  · intro c hc
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hc
    have hi := List.mem_range.mp hi
    have := pow_e_anti he (show i + 1 ≤ K by omega) le_rfl
    refine Finset.disjoint_left.mpr fun ℓ h1 h2 => ?_
    simp only [botT, midT, Finset.mem_filter] at h1 h2
    omega
  · rw [List.pairwise_map]
    refine (List.pairwise_lt_range (n := K)).imp_of_mem fun {i j} hi hj hij => ?_
    have hj := List.mem_range.mp hj
    have := pow_e_anti he (show i + 1 ≤ j by omega) (by omega)
    refine Finset.disjoint_left.mpr fun ℓ h1 h2 => ?_
    simp only [midT, Finset.mem_filter] at h1 h2
    omega

lemma blocksT_supp : supp (blocksT P e lev K kbot) = P := by
  ext ℓ
  rw [mem_supp]
  constructor
  · rintro ⟨b, hb, hℓ⟩
    simp only [blocksT, List.mem_cons, List.mem_map, List.mem_range] at hb
    rcases hb with rfl | rfl | ⟨i, _, rfl⟩ <;> exact (Finset.mem_filter.mp hℓ).1
  · intro hℓ
    by_cases htop : 2 ^ e 0 < ℓ
    · exact ⟨topT P e, by simp [blocksT], Finset.mem_filter.mpr ⟨hℓ, htop⟩⟩
    by_cases hbot : ℓ ≤ 2 ^ e K
    · exact ⟨botT P e K kbot, by simp [blocksT], Finset.mem_filter.mpr ⟨hℓ, hbot⟩⟩
    push Not at htop hbot
    have hex : ∃ i, 2 ^ e (i + 1) < ℓ ∨ K ≤ i := ⟨K, Or.inr le_rfl⟩
    classical
    set i := Nat.find hex with hidef
    have hspec := Nat.find_spec hex
    have hiK : i < K := by
      by_contra h
      push Not at h
      -- then `i = K`... minimality at `K - 1`
      have hK0 : 0 < K := by
        rcases Nat.eq_zero_or_pos K with h0 | h0
        · rw [h0] at hbot; omega
        · exact h0
      have := Nat.find_min hex (show K - 1 < i by omega)
      push Not at this
      rw [show K - 1 + 1 = K by omega] at this
      omega
    have h1 : 2 ^ e (i + 1) < ℓ := by
      rcases hspec with h | h
      · exact h
      · omega
    have h2 : ℓ ≤ 2 ^ e i := by
      rcases Nat.eq_zero_or_pos i with h0 | h0
      · rw [h0]; exact htop
      · have := Nat.find_min hex (show i - 1 < i by omega)
        push Not at this
        rw [show i - 1 + 1 = i by omega] at this
        exact this.1
    exact ⟨midT P e lev i, List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_map.mpr ⟨i, List.mem_range.mpr hiK, rfl⟩)), Finset.mem_filter.mpr ⟨hℓ, h1, h2⟩⟩

end Blocks

/-! ### Per-block estimates -/

/-- Mertens bound for an interval block, shells of width `lo / 256`. -/
theorem sigma_interval_le (S : Finset ℕ) (hS : ∀ ℓ ∈ S, ℓ.Prime) (lo hi : ℕ) (hlo : 512 ≤ lo)
    (hlh : lo ≤ hi) (hrange : ∀ ℓ ∈ S, 2 ^ lo < ℓ ∧ ℓ ≤ 2 ^ hi) :
    ∑ ℓ ∈ S, recip ℓ ≤ Real.log hi - Real.log lo + ((hi : ℝ) - lo) / (256 * lo)
      + c₁ * (512 * ((hi : ℝ) - lo) / lo + 1) / lo := by
  set w := lo / 256 with hw
  have hw1 : 1 ≤ w := by rw [hw]; omega
  have h := sum_inv_blockM_le w hw1 (hi - lo) lo hi rfl S hS (by omega) hlh hrange
  have hloR : (512 : ℝ) ≤ lo := by exact_mod_cast hlo
  have hlhR : (lo : ℝ) ≤ hi := by exact_mod_cast hlh
  have hwR : (w : ℝ) ≤ lo / 256 := by
    rw [hw, le_div_iff₀ (by norm_num)]; exact_mod_cast Nat.div_mul_le_self lo 256
  have hwR2 : (lo : ℝ) / 512 ≤ w := by
    rw [hw, div_le_iff₀ (by norm_num)]
    have := Nat.lt_div_mul_add (a := lo) (show 0 < 256 by norm_num)
    have : (lo : ℝ) < (lo / 256 : ℕ) * 256 + 256 := by exact_mod_cast this
    have : (256 : ℝ) ≤ (lo / 256 : ℕ) * 256 := by
      have : 1 ≤ lo / 256 := by omega
      have : (1 : ℝ) ≤ (lo / 256 : ℕ) := by exact_mod_cast this
      linarith
    linarith
  have hwpos : (0 : ℝ) < w := by exact_mod_cast hw1
  have hc := c₁_pos
  have hd : (0 : ℝ) ≤ hi - lo := by linarith
  simp only [recip]
  refine h.trans ?_
  have e1 : (w : ℝ) * (hi - lo) / (lo : ℝ) ^ 2 ≤ ((hi : ℝ) - lo) / (256 * lo) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have : (w : ℝ) * 256 ≤ lo := by linarith
    nlinarith [mul_le_mul_of_nonneg_right this (mul_nonneg hd (by positivity : (0 : ℝ) ≤ lo))]
  have e2 : c₁ * (((hi : ℝ) - lo) / w + 1) / lo ≤ c₁ * (512 * ((hi : ℝ) - lo) / lo + 1) / lo := by
    apply div_le_div_of_nonneg_right _ (by positivity)
    apply mul_le_mul_of_nonneg_left _ hc.le
    have : ((hi : ℝ) - lo) / w ≤ 512 * ((hi : ℝ) - lo) / lo := by
      rw [div_le_div_iff₀ hwpos (by positivity)]
      nlinarith
    linarith
  linarith

/-- Ratio bound for a block of level `k` (degree `2k+1`), all primes above `2^lo`. -/
theorem ratio_le_of_sigma (B : Finset ℕ) (k lo : ℕ) (hlo : 2 ≤ lo)
    (hB : ∀ ℓ ∈ B, ℓ.Prime ∧ 2 ^ lo < ℓ) :
    Eb (B, k) recip / Ub (B, k) recip ≤
      (∑ ℓ ∈ B, recip ℓ) ^ (2 * k + 1) / (2 * k + 1).factorial *
        Real.exp ((1 + 1 / 2 ^ lo) * ∑ ℓ ∈ B, recip ℓ) := by
  have hpow : (4 : ℝ) ≤ 2 ^ lo := by
    calc (4 : ℝ) = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ lo := pow_le_pow_right₀ (by norm_num) hlo
  have hη3 : (1 : ℝ) / 2 ^ lo ≤ 1 / 3 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
  have hy : ∀ ℓ ∈ B, 0 ≤ recip ℓ ∧ recip ℓ ≤ 1 / 2 ^ lo := by
    intro ℓ h
    obtain ⟨hp, hl⟩ := hB ℓ h
    have : (2 : ℝ) ^ lo < ℓ := by exact_mod_cast hl
    exact ⟨by unfold recip; positivity,
      one_div_le_one_div_of_le (by positivity) this.le⟩
  have hy2 : ∀ ℓ ∈ B, 0 ≤ recip ℓ ∧ recip ℓ ≤ 1 / 2 := fun ℓ h =>
    ⟨(hy ℓ h).1, (hy ℓ h).2.trans (by linarith)⟩
  refine (Eb_div_Ub_le recip (B, k) hy2).trans ?_
  exact E_div_prod_le' (2 * k + 1) B recip hη3 hy

/-- Level 1: the ratio is the sum. -/
lemma ratio_topT (B : Finset ℕ) : Eb (B, 0) recip / Ub (B, 0) recip = ∑ ℓ ∈ B, recip ℓ :=
  Eb_div_Ub_level_one recip B

/-- An exact block has `e = 0`. -/
lemma ratio_exact (B : Finset ℕ) (k : ℕ) (hk : B.card < 2 * k + 1) :
    Eb (B, k) recip / Ub (B, k) recip = 0 := by
  have : Eb (B, k) recip = 0 := by
    unfold Eb E
    rw [Finset.powersetCard_eq_empty.mpr hk]
    simp
  rw [this, zero_div]

end Shoup.Sieve
