import Shoup.Sieve.Main
import Shoup.Sieve.Primes

/-!
# A polynomial-in-`ω` bound for the least primitive root under GRH

`polyOmega_of_GRH : PolyOmegaStatement 136`, i.e. `g(p) ≤ C ω(p-1)^136 (log p)²`.

Blocks for `P = primeFactors(p - 1)`, `r = |P|`, `t` least with `16 r ≤ 2^{2^t}`:

* top: `ℓ > 2^{2^t}`, level 1 (union bound); `Σ 1/ℓ ≤ r/2^{2^t} ≤ 1/16`, so `e/A ≤ 1/15`;
* bottom: `ℓ ≤ 2`, level 3 (exact);
* middle `i < t`: `2^{2^i} < ℓ ≤ 2^{2^{i+1}}`, level `2(t-1-i) + 19`; `Σ 1/ℓ ≤ 4` (Chebyshev),
  so `e/A ≤ e^{28}/5^{level}` (`E_div_prod_le` with `t = 5`), summing to `< 1/5`.

The masses multiply to `≤ (r+1)^{21} · 8 · 2^{46·2^{t-1}} ≤ 8 (r+1)^{21} (16 r)^{46}`, the
number of blocks is `t + 2 ≤ 19 r - 1`, and `∏_{ℓ∈P}(1 - 1/ℓ) ≥ 1/(r+1)`; the sieve inequality
`le_of_no_primitive_root_lt` then gives `x ≤ C r^{136} (log p)²`.
-/

namespace Shoup.Sieve

open Finset ArithmeticFunction Erdos985
open scoped ArithmeticFunction.omega

/-! ### Generic lemmas on block lists -/

lemma mem_supp {bs : List Block} {ℓ : ℕ} : ℓ ∈ supp bs ↔ ∃ b ∈ bs, ℓ ∈ b.1 := by
  induction bs with
  | nil => simp [supp]
  | cons b bs ih => simp [supp, ih]

lemma disj_of_pairwise {bs : List Block} (h : bs.Pairwise fun b c => Disjoint b.1 c.1) :
    Disj bs := by
  induction bs with
  | nil => trivial
  | cons b bs ih =>
    rw [List.pairwise_cons] at h
    refine ⟨Finset.disjoint_left.mpr fun ℓ hb hs => ?_, ih h.2⟩
    obtain ⟨c, hc, hℓc⟩ := mem_supp.mp hs
    exact Finset.disjoint_left.mp (h.1 c hc) hb hℓc

lemma prodA_eq_prod {bs : List Block} (hd : Disj bs) (y : ℕ → ℝ) :
    prodA bs y = ∏ ℓ ∈ supp bs, (1 - y ℓ) := by
  induction bs with
  | nil => simp [prodA, supp]
  | cons b bs ih =>
    simp only [prodA, supp, Ab]
    rw [Finset.prod_union hd.1, ih hd.2]

lemma ratioSum_append (L₁ L₂ : List Block) (y : ℕ → ℝ) :
    ratioSum (L₁ ++ L₂) y = ratioSum L₁ y + ratioSum L₂ y := by
  induction L₁ with
  | nil => simp [ratioSum]
  | cons b L ih => simp only [List.cons_append, ratioSum, ih]; ring

lemma massBound_append (L₁ L₂ : List Block) :
    massBound (L₁ ++ L₂) = massBound L₁ * massBound L₂ := by
  induction L₁ with
  | nil => simp [massBound]
  | cons b L ih => simp only [List.cons_append, massBound, ih]; ring

lemma ratioSum_map_range (g : ℕ → Block) (t : ℕ) (y : ℕ → ℝ) :
    ratioSum ((List.range t).map g) y = ∑ i ∈ range t, Eb (g i) y / Ab (g i) y := by
  induction t with
  | zero => simp [ratioSum]
  | succ t ih =>
    rw [List.range_succ, List.map_append, ratioSum_append, ih, Finset.sum_range_succ]
    simp [ratioSum]

lemma massBound_map_range (g : ℕ → Block) (t : ℕ) :
    massBound ((List.range t).map g) =
      ∏ i ∈ range t, ((g i).1.card + 1 : ℝ) ^ (2 * (g i).2 + 1) := by
  induction t with
  | zero => simp [massBound]
  | succ t ih =>
    rw [List.range_succ, List.map_append, massBound_append, ih, Finset.prod_range_succ]
    simp [massBound]

/-! ### The blocks -/

section Blocks

variable (P : Finset ℕ) (t : ℕ)

def topB : Block := (P.filter fun ℓ => 2 ^ 2 ^ t < ℓ, 0)
def botB : Block := (P.filter fun ℓ => ℓ ≤ 2, 1)
def midB (i : ℕ) : Block :=
  (P.filter fun ℓ => 2 ^ 2 ^ i < ℓ ∧ ℓ ≤ 2 ^ (2 * 2 ^ i), t - 1 - i + 9)

def blocks : List Block := topB P t :: botB P :: (List.range t).map (midB P t)

lemma two_le_pow_pow (i : ℕ) : 2 ≤ 2 ^ 2 ^ i := by
  calc 2 = 2 ^ 1 := by norm_num
    _ ≤ 2 ^ 2 ^ i := Nat.pow_le_pow_right (by norm_num) (Nat.one_le_two_pow)

lemma pow_two_mul_le {i j : ℕ} (h : i < j) : 2 ^ (2 * 2 ^ i) ≤ 2 ^ 2 ^ j := by
  apply Nat.pow_le_pow_right (by norm_num)
  calc 2 * 2 ^ i = 2 ^ (i + 1) := by ring
    _ ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) h

lemma blocks_disj : Disj (blocks P t) := by
  apply disj_of_pairwise
  have hmid : ∀ i, 2 ≤ 2 ^ 2 ^ i := two_le_pow_pow
  refine List.Pairwise.cons ?_ (List.Pairwise.cons ?_ ?_)
  · intro c hc
    rcases List.mem_cons.mp hc with rfl | hc
    · refine Finset.disjoint_left.mpr fun ℓ h1 h2 => ?_
      simp only [topB, botB, Finset.mem_filter] at h1 h2
      have := hmid t
      omega
    · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hc
      have := pow_two_mul_le (List.mem_range.mp hi)
      refine Finset.disjoint_left.mpr fun ℓ h1 h2 => ?_
      simp only [topB, midB, Finset.mem_filter] at h1 h2
      omega
  · intro c hc
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp hc
    have := hmid i
    refine Finset.disjoint_left.mpr fun ℓ h1 h2 => ?_
    simp only [botB, midB, Finset.mem_filter] at h1 h2
    omega
  · rw [List.pairwise_map]
    refine (List.pairwise_lt_range (n := t)).imp fun {i j} hij => ?_
    have := pow_two_mul_le hij
    refine Finset.disjoint_left.mpr fun ℓ h1 h2 => ?_
    simp only [midB, Finset.mem_filter] at h1 h2
    omega

lemma blocks_supp : supp (blocks P t) = P := by
  ext ℓ
  rw [mem_supp]
  constructor
  · rintro ⟨b, hb, hℓ⟩
    simp only [blocks, List.mem_cons, List.mem_map, List.mem_range] at hb
    rcases hb with rfl | rfl | ⟨i, _, rfl⟩ <;> exact (Finset.mem_filter.mp hℓ).1
  · intro hℓ
    by_cases h2 : ℓ ≤ 2
    · exact ⟨botB P, by simp [blocks], Finset.mem_filter.mpr ⟨hℓ, h2⟩⟩
    by_cases htop : 2 ^ 2 ^ t < ℓ
    · exact ⟨topB P t, by simp [blocks], Finset.mem_filter.mpr ⟨hℓ, htop⟩⟩
    push_neg at h2 htop
    have hex : ∃ i, ℓ ≤ 2 ^ (2 * 2 ^ i) :=
      ⟨t, htop.trans (Nat.pow_le_pow_right (by norm_num) (by omega))⟩
    classical
    set i := Nat.find hex with hi
    have hi1 : ℓ ≤ 2 ^ (2 * 2 ^ i) := Nat.find_spec hex
    have hit : i < t := by
      rcases Nat.eq_zero_or_pos t with ht | ht
      · subst ht; simp at htop; omega
      · have : ℓ ≤ 2 ^ (2 * 2 ^ (t - 1)) := by
          rw [show 2 * 2 ^ (t - 1) = 2 ^ t by
            rw [← pow_succ']; congr 1; omega]
          exact htop
        exact lt_of_le_of_lt (Nat.find_min' hex this) (by omega)
    have hi2 : 2 ^ 2 ^ i < ℓ := by
      rcases Nat.eq_zero_or_pos i with h0 | h0
      · rw [h0]; simpa using h2
      · have := Nat.find_min hex (show i - 1 < i by omega)
        push_neg at this
        rwa [show 2 * 2 ^ (i - 1) = 2 ^ i by rw [← pow_succ']; congr 1; omega] at this
    exact ⟨midB P t i, List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_map.mpr ⟨i, List.mem_range.mpr hit, rfl⟩)), Finset.mem_filter.mpr ⟨hℓ, hi2, hi1⟩⟩

end Blocks

/-! ### The ratio sum -/

section Ratio

variable {p : ℕ}

lemma ratio_top (hp : p.Prime) (t : ℕ) (ht : 16 * (p - 1).primeFactors.card ≤ 2 ^ 2 ^ t) :
    Eb (topB (p - 1).primeFactors t) recip / Ab (topB (p - 1).primeFactors t) recip ≤ 1 / 15 := by
  set B := (topB (p - 1).primeFactors t).1 with hB
  have hy : ∀ ℓ ∈ B, 0 ≤ recip ℓ ∧ recip ℓ ≤ 1 := fun ℓ h =>
    have := recip_mem (Nat.mem_primeFactors.mp (Finset.mem_filter.mp h).1).1
    ⟨this.1, by linarith [this.2]⟩
  have hE : Eb (topB (p - 1).primeFactors t) recip = ∑ ℓ ∈ B, recip ℓ := by
    simp only [Eb, topB, mul_zero, zero_add]; exact E_one _ _
  have hZ : (0 : ℝ) < 2 ^ 2 ^ t := by positivity
  have hσ : ∑ ℓ ∈ B, recip ℓ ≤ 1 / 16 := by
    calc ∑ ℓ ∈ B, recip ℓ ≤ ∑ _ℓ ∈ B, 1 / (2 ^ 2 ^ t : ℝ) := by
          refine Finset.sum_le_sum fun ℓ h => ?_
          have h1 : (2 ^ 2 ^ t : ℝ) < ℓ := by exact_mod_cast (Finset.mem_filter.mp h).2
          exact one_div_le_one_div_of_le hZ h1.le
      _ = B.card / (2 ^ 2 ^ t : ℝ) := by rw [Finset.sum_const, nsmul_eq_mul]; ring
      _ ≤ (p - 1).primeFactors.card / (2 ^ 2 ^ t : ℝ) := by
          gcongr; exact Finset.filter_subset _ _
      _ ≤ 1 / 16 := by
          rw [div_le_div_iff₀ hZ (by norm_num)]
          have : (16 * (p - 1).primeFactors.card : ℝ) ≤ 2 ^ 2 ^ t := by exact_mod_cast ht
          linarith
  have hA : 1 - ∑ ℓ ∈ B, recip ℓ ≤ Ab (topB (p - 1).primeFactors t) recip := by
    have h1 := G_even_le_prod B recip hy 0
    have h2 := G_succ 1 B recip
    rw [G_one, E_one] at h2
    simp only [Ab, ← hB]
    norm_num at h1 h2
    linarith
  rw [hE, div_le_iff₀ (by linarith [Finset.sum_nonneg fun ℓ h => (hy ℓ h).1])]
  linarith

lemma ratio_bot (y : ℕ → ℝ) :
    Eb (botB (p - 1).primeFactors) y / Ab (botB (p - 1).primeFactors) y = 0 := by
  have hcard : (botB (p - 1).primeFactors).1.card ≤ 1 := by
    have : (botB (p - 1).primeFactors).1 ⊆ {2} := by
      intro ℓ h
      obtain ⟨h1, h2⟩ := Finset.mem_filter.mp h
      have := (Nat.mem_primeFactors.mp h1).1.two_le
      rw [Finset.mem_singleton]; omega
    simpa using Finset.card_le_card this
  have : Eb (botB (p - 1).primeFactors) y = 0 := by
    unfold Eb E
    rw [Finset.powersetCard_eq_empty.mpr (by simp only [botB] at hcard ⊢; omega)]
    simp
  rw [this, zero_div]

lemma exp28_le : Real.exp 28 / 5 ^ 19 ≤ 1 / 10 := by
  have h := Real.exp_one_lt_d9
  have h28 : Real.exp 28 = Real.exp 1 ^ 28 := by rw [← Real.exp_nat_mul]; norm_num
  rw [h28, div_le_iff₀ (by norm_num)]
  calc Real.exp 1 ^ 28 ≤ (2.7182818286 : ℝ) ^ 28 :=
        pow_le_pow_left₀ (Real.exp_pos 1).le h.le 28
    _ ≤ 1 / 10 * 5 ^ 19 := by norm_num

lemma ratio_mid (hp : p.Prime) (t i : ℕ) :
    Eb (midB (p - 1).primeFactors t i) recip / Ab (midB (p - 1).primeFactors t i) recip ≤
      Real.exp 28 / 5 ^ (2 * (t - 1 - i) + 19) := by
  set B := (midB (p - 1).primeFactors t i).1 with hB
  have hy : ∀ ℓ ∈ B, 0 ≤ recip ℓ ∧ recip ℓ ≤ 1 / 2 := fun ℓ h =>
    recip_mem (Nat.mem_primeFactors.mp (Finset.mem_filter.mp h).1).1
  have hσ : ∑ ℓ ∈ B, recip ℓ ≤ 4 :=
    sum_inv_block_le B (fun ℓ h => (Nat.mem_primeFactors.mp (Finset.mem_filter.mp h).1).1)
      (2 ^ i) Nat.one_le_two_pow fun ℓ h => (Finset.mem_filter.mp h).2
  have h := E_div_prod_le (2 * (midB (p - 1).primeFactors t i).2 + 1) B recip hy
    (t := 5) (by norm_num)
  simp only [midB] at h ⊢
  refine h.trans ?_
  rw [show 2 * (t - 1 - i + 9) + 1 = 2 * (t - 1 - i) + 19 by ring]
  gcongr
  linarith

lemma ratioSum_blocks_le (hp : p.Prime) (t : ℕ)
    (ht : 16 * (p - 1).primeFactors.card ≤ 2 ^ 2 ^ t) :
    ratioSum (blocks (p - 1).primeFactors t) recip ≤ 1 / 2 := by
  simp only [blocks, ratioSum]
  rw [ratioSum_map_range, ratio_bot]
  have h1 := ratio_top hp t ht
  have h2 : ∑ i ∈ range t, Eb (midB (p - 1).primeFactors t i) recip /
      Ab (midB (p - 1).primeFactors t i) recip ≤ 1 / 5 := by
    calc _ ≤ ∑ i ∈ range t, Real.exp 28 / 5 ^ (2 * (t - 1 - i) + 19) :=
          Finset.sum_le_sum fun i _ => ratio_mid hp t i
      _ = ∑ u ∈ range t, Real.exp 28 / 5 ^ (2 * u + 19) := by
          rw [← Finset.sum_range_reflect]
          refine Finset.sum_congr rfl fun u hu => ?_
          have := Finset.mem_range.mp hu
          congr 3; omega
      _ ≤ ∑ u ∈ range t, (Real.exp 28 / 5 ^ 19) * (1 / 2) ^ u := by
          refine Finset.sum_le_sum fun u _ => ?_
          have he : 0 ≤ Real.exp 28 := (Real.exp_pos _).le
          have hden : (5 : ℝ) ^ 19 * 2 ^ u ≤ 5 ^ (2 * u + 19) := by
            rw [pow_add, pow_mul, mul_comm]
            have : (2 : ℝ) ^ u ≤ (5 ^ 2) ^ u := pow_le_pow_left₀ (by norm_num) (by norm_num) u
            have h5 : (0 : ℝ) < 5 ^ 19 := by positivity
            nlinarith
          calc Real.exp 28 / 5 ^ (2 * u + 19) ≤ Real.exp 28 / (5 ^ 19 * 2 ^ u) :=
                div_le_div_of_nonneg_left he (by positivity) hden
            _ = (Real.exp 28 / 5 ^ 19) * (1 / 2) ^ u := by rw [one_div_pow]; field_simp
      _ = (Real.exp 28 / 5 ^ 19) * ∑ u ∈ range t, (1 / 2 : ℝ) ^ u := by rw [Finset.mul_sum]
      _ ≤ (1 / 10) * 2 :=
          mul_le_mul exp28_le (sum_geometric_two_le t) (Finset.sum_nonneg fun _ _ => by positivity)
            (by norm_num)
      _ = 1 / 5 := by norm_num
  linarith

end Ratio

/-! ### The mass -/

lemma sum_two_pow_add_one (T : ℕ) : ∑ i ∈ range T, 2 ^ i + 1 = 2 ^ T := by
  induction T with
  | zero => simp
  | succ T ih => rw [Finset.sum_range_succ, pow_succ]; omega

lemma sum_pow_weight_le (T : ℕ) :
    ∑ i ∈ range T, 2 * 2 ^ i * (2 * (T - i) + 19) ≤ 46 * 2 ^ T := by
  induction T with
  | zero => simp
  | succ T ih =>
    rw [Finset.sum_range_succ]
    have hsplit : ∑ i ∈ range T, 2 * 2 ^ i * (2 * (T + 1 - i) + 19) =
        ∑ i ∈ range T, 2 * 2 ^ i * (2 * (T - i) + 19) + 4 * ∑ i ∈ range T, 2 ^ i := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i hi => ?_
      have := Finset.mem_range.mp hi
      rw [show 2 * (T + 1 - i) + 19 = (2 * (T - i) + 19) + 2 by omega]
      ring
    rw [hsplit, show T + 1 - T = 1 by omega, pow_succ]
    have := sum_two_pow_add_one T
    omega

lemma massBound_blocks_le (P : Finset ℕ) (hP : ∀ ℓ ∈ P, 2 ≤ ℓ) (T : ℕ) (R : ℝ)
    (hR : (2 : ℝ) ^ 2 ^ T ≤ R) :
    massBound (blocks P (T + 1)) ≤
      ((P.card : ℝ) + 1) * 8 * ((P.card : ℝ) + 1) ^ 19 * R ^ 46 := by
  have hr0 : (0 : ℝ) ≤ P.card := Nat.cast_nonneg _
  simp only [blocks, massBound]
  rw [massBound_map_range, Finset.prod_range_succ]
  -- top block
  have htop : ((topB P (T + 1)).1.card + 1 : ℝ) ^ (2 * (topB P (T + 1)).2 + 1) ≤ P.card + 1 := by
    simp only [topB, mul_zero, zero_add, pow_one]
    have : ((P.filter fun ℓ => 2 ^ 2 ^ (T + 1) < ℓ).card : ℝ) ≤ P.card := by
      exact_mod_cast Finset.card_filter_le _ _
    linarith
  -- bottom block
  have hbot : ((botB P).1.card + 1 : ℝ) ^ (2 * (botB P).2 + 1) ≤ 8 := by
    have hc : (botB P).1.card ≤ 1 := by
      have : (botB P).1 ⊆ {2} := by
        intro ℓ h
        obtain ⟨h1, h2⟩ := Finset.mem_filter.mp h
        have := hP ℓ h1
        rw [Finset.mem_singleton]; omega
      simpa using Finset.card_le_card this
    have : ((botB P).1.card : ℝ) ≤ 1 := by exact_mod_cast hc
    simp only [botB] at this ⊢
    calc ((P.filter fun ℓ => ℓ ≤ 2).card + 1 : ℝ) ^ (2 * 1 + 1) ≤ 2 ^ (2 * 1 + 1) :=
          pow_le_pow_left₀ (by positivity) (by linarith) _
      _ = 8 := by norm_num
  -- the top middle block
  have hlast : ((midB P (T + 1) T).1.card + 1 : ℝ) ^ (2 * (midB P (T + 1) T).2 + 1) ≤
      ((P.card : ℝ) + 1) ^ 19 := by
    simp only [midB, show T + 1 - 1 - T = 0 by omega]
    refine pow_le_pow_left₀ (by positivity) ?_ _
    have : ((P.filter fun ℓ => 2 ^ 2 ^ T < ℓ ∧ ℓ ≤ 2 ^ (2 * 2 ^ T)).card : ℝ) ≤ P.card := by
      exact_mod_cast Finset.card_filter_le _ _
    linarith
  -- the lower middle blocks
  have hlow : ∏ i ∈ range T, ((midB P (T + 1) i).1.card + 1 : ℝ) ^ (2 * (midB P (T + 1) i).2 + 1)
      ≤ R ^ 46 := by
    calc ∏ i ∈ range T, ((midB P (T + 1) i).1.card + 1 : ℝ) ^ (2 * (midB P (T + 1) i).2 + 1)
        ≤ ∏ i ∈ range T, (2 : ℝ) ^ (2 * 2 ^ i * (2 * (T - i) + 19)) := by
          refine Finset.prod_le_prod₀ (fun i _ => by positivity) fun i hi => ?_
          have hiT := Finset.mem_range.mp hi
          have hc := card_block_add_one_le (midB P (T + 1) i).1 (2 ^ i)
            fun ℓ h => (Finset.mem_filter.mp h).2
          have hcR : ((midB P (T + 1) i).1.card + 1 : ℝ) ≤ (2 : ℝ) ^ (2 * 2 ^ i) := by
            exact_mod_cast hc
          rw [pow_mul]
          simp only [midB]
          rw [show 2 * (T + 1 - 1 - i + 9) + 1 = 2 * (T - i) + 19 by omega]
          exact pow_le_pow_left₀ (by positivity) hcR _
      _ = (2 : ℝ) ^ (∑ i ∈ range T, 2 * 2 ^ i * (2 * (T - i) + 19)) :=
          Finset.prod_pow_eq_pow_sum _ _ _
      _ ≤ (2 : ℝ) ^ (46 * 2 ^ T) := pow_le_pow_right₀ (by norm_num) (sum_pow_weight_le T)
      _ = ((2 : ℝ) ^ 2 ^ T) ^ 46 := by rw [← pow_mul, mul_comm]
      _ ≤ R ^ 46 := pow_le_pow_left₀ (by positivity) hR _
  have h0 : ∀ i ∈ range T, (0 : ℝ) ≤
      ((midB P (T + 1) i).1.card + 1 : ℝ) ^ (2 * (midB P (T + 1) i).2 + 1) :=
    fun i _ => by positivity
  have hP0 := Finset.prod_nonneg h0
  have hR0 : (0 : ℝ) ≤ R ^ 46 := hP0.trans hlow
  have hb0 : (0 : ℝ) ≤ ((botB P).1.card + 1 : ℝ) ^ (2 * (botB P).2 + 1) := by positivity
  have hl0 : (0 : ℝ) ≤ ((midB P (T + 1) T).1.card + 1 : ℝ) ^ (2 * (midB P (T + 1) T).2 + 1) := by
    positivity
  calc _ ≤ ((P.card : ℝ) + 1) * (8 * (R ^ 46 * ((P.card : ℝ) + 1) ^ 19)) := by
        gcongr
    _ = _ := by ring

/-! ### The theorem -/

/-- `16^46`, kept as an atom so that `ring` does not expand it. -/
noncomputable irreducible_def c16 : ℝ := 16 ^ 46

lemma c16_pos : 0 < c16 := by rw [c16_def]; positivity

/-- The polynomial constant: `x ≤ polyC · r^136 (log p)²`, `polyC = 1089 (304 · 2^21 · 16^46)²`. -/
noncomputable irreducible_def polyC : ℝ := 1089 * (304 * 2 ^ 21 * c16) ^ 2

theorem le_of_no_primitive_root_lt_poly (hGRH : DirichletLNonvanishingRightOfHalf)
    (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (x : ℕ) (hx1 : 1 ≤ x) (hxp : x ≤ p)
    (hno : ∀ g : ℕ, 0 < g → g < x → orderOf (g : ZMod p) ≠ p - 1) :
    (x : ℝ) ≤ polyC * (ω (p - 1) : ℝ) ^ 136 * Real.log p ^ 2 := by
  have h3 : 3 ≤ p := by have := hp.two_le; omega
  set P := (p - 1).primeFactors with hPdef
  set r := P.card with hrdef
  have hr1 : 1 ≤ r := Shoup.one_le_card_primeFactors p hp hp2
  have hP2 : ∀ ℓ ∈ P, 2 ≤ ℓ := fun ℓ h => (Nat.mem_primeFactors.mp h).1.two_le
  -- choose `t`
  have hex : ∃ t, 16 * r ≤ 2 ^ 2 ^ t := ⟨16 * r, by
    have h1 := Nat.lt_two_pow_self (n := 16 * r)
    have h2 := Nat.lt_two_pow_self (n := 2 ^ (16 * r))
    omega⟩
  classical
  set t := Nat.find hex with htdef
  have ht : 16 * r ≤ 2 ^ 2 ^ t := Nat.find_spec hex
  have ht1 : 1 ≤ t := by
    rcases Nat.eq_zero_or_pos t with h | h
    · rw [h] at ht; simp at ht; omega
    · exact h
  obtain ⟨T, hT⟩ : ∃ T, t = T + 1 := ⟨t - 1, by omega⟩
  have hTmin : 2 ^ 2 ^ T < 16 * r := by
    have := Nat.find_min hex (show T < Nat.find hex by omega)
    exact not_le.mp this
  rw [hT] at ht
  set bs := blocks P (T + 1) with hbs
  have hd := blocks_disj P (T + 1)
  have hsupp := blocks_supp P (T + 1)
  have hR := ratioSum_blocks_le hp (T + 1) ht
  have key := le_of_no_primitive_root_lt hGRH p hp hp2 x hx1 hxp hno bs hd hsupp hR
  -- bounds on the pieces
  have hrR : (1 : ℝ) ≤ r := by exact_mod_cast hr1
  have hθ : 1 / ((r : ℝ) + 1) ≤ prodA bs recip := by
    rw [prodA_eq_prod hd, hsupp]
    simpa [recip] using prod_one_sub_inv_ge P hP2
  have hθpos : 0 < prodA bs recip := lt_of_lt_of_le (by positivity) hθ
  have hlen : (bs.length + 1 : ℝ) ≤ 19 * r := by
    have : bs.length = T + 3 := by simp [hbs, blocks]
    rw [this]
    have h1 : T < 2 ^ T := Nat.lt_two_pow_self
    have h2 : 2 ^ T < 2 ^ 2 ^ T := Nat.lt_two_pow_self
    have : T + 3 + 1 ≤ 19 * r := by omega
    exact_mod_cast this
  have hmass : massBound bs ≤ ((r : ℝ) + 1) * 8 * ((r : ℝ) + 1) ^ 19 * (16 * r) ^ 46 := by
    refine massBound_blocks_le P hP2 T (16 * r) ?_
    exact_mod_cast hTmin.le
  set L := Real.log p with hLdef
  have hL : 0 ≤ L := Real.log_nonneg (by exact_mod_cast hp.one_lt.le)
  have hM0 : 0 ≤ massBound bs := massBound_nonneg bs
  -- `2 (J+1) M L / θ ≤ 304 · 2^21 · 16^46 · r^68 L`
  have hc0 := c16_pos
  have hm' : massBound bs ≤ ((r : ℝ) + 1) * 8 * ((r : ℝ) + 1) ^ 19 * (c16 * (r : ℝ) ^ 46) := by
    rw [mul_pow, ← c16_def] at hmass; exact hmass
  set Y : ℝ := (304 * 2 ^ 21 * c16) * (r : ℝ) ^ 68 * L with hY
  have hK : 2 * ((bs.length + 1 : ℝ) * massBound bs) * L / prodA bs recip ≤ Y := by
    rw [div_le_iff₀ hθpos]
    have hr2 : (r : ℝ) + 1 ≤ 2 * r := by linarith
    have hinv : 1 ≤ ((r : ℝ) + 1) * prodA bs recip := by
      rw [div_le_iff₀ (by positivity)] at hθ; linarith
    have hJML0 : 0 ≤ 2 * ((bs.length + 1 : ℝ) * massBound bs) * L := by positivity
    set X1 : ℝ := 2 * (19 * r * (((r : ℝ) + 1) * 8 * ((r : ℝ) + 1) ^ 19 * (c16 * (r : ℝ) ^ 46)))
      * L with hX1
    have h1 : 2 * ((bs.length + 1 : ℝ) * massBound bs) * L ≤ X1 := by
      rw [hX1]; gcongr
    have h2 : X1 * ((r : ℝ) + 1) ≤ Y := by
      rw [show X1 * ((r : ℝ) + 1) = 304 * c16 * (r : ℝ) ^ 47 * ((r : ℝ) + 1) ^ 21 * L by
            rw [hX1]; ring,
        show Y = 304 * c16 * (r : ℝ) ^ 47 * (2 * r) ^ 21 * L by rw [hY]; ring]
      gcongr
    calc 2 * ((bs.length + 1 : ℝ) * massBound bs) * L
        ≤ 2 * ((bs.length + 1 : ℝ) * massBound bs) * L * (((r : ℝ) + 1) * prodA bs recip) :=
          le_mul_of_one_le_right hJML0 hinv
      _ ≤ X1 * (((r : ℝ) + 1) * prodA bs recip) :=
          mul_le_mul_of_nonneg_right h1 (by positivity)
      _ = (X1 * ((r : ℝ) + 1)) * prodA bs recip := by ring
      _ ≤ Y * prodA bs recip := mul_le_mul_of_nonneg_right h2 hθpos.le
  have hK0 : 0 ≤ 2 * ((bs.length + 1 : ℝ) * massBound bs) * L / prodA bs recip := by
    positivity
  calc (x : ℝ) ≤ 1089 * (2 * ((bs.length + 1 : ℝ) * massBound bs) * L / prodA bs recip) ^ 2 :=
        key
    _ ≤ 1089 * Y ^ 2 := by gcongr
    _ = polyC * (ω (p - 1) : ℝ) ^ 136 * L ^ 2 := by
        rw [cardDistinctFactors_eq_card_primeFactors, polyC_def, hY]; ring

end Shoup.Sieve

namespace Shoup

open Sieve
open scoped ArithmeticFunction.omega

/-- From "no primitive root below `x` forces `x ≤ B`" to "a primitive root `≤ B`". -/
lemma hasPrimitiveRootLE_of_bound (p : ℕ) (hp : p.Prime) (B : ℝ) (hB0 : 0 ≤ B)
    (h : ∀ x : ℕ, 1 ≤ x → x ≤ p → (∀ g : ℕ, 0 < g → g < x → orderOf (g : ZMod p) ≠ p - 1) →
      (x : ℝ) ≤ B) :
    HasPrimitiveRootLE p B := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hlt : B < ((⌊B⌋₊ + 1 : ℕ) : ℝ) := by
    rw [Nat.cast_add, Nat.cast_one]; exact Nat.lt_floor_add_one B
  have hfl : ∀ g : ℕ, g < ⌊B⌋₊ + 1 → (g : ℝ) ≤ B := fun g hg =>
    (Nat.cast_le.mpr (Nat.lt_succ_iff.mp hg)).trans (Nat.floor_le hB0)
  by_cases hXp : ⌊B⌋₊ + 1 ≤ p
  · by_contra hcon
    have hno : ∀ g : ℕ, 0 < g → g < ⌊B⌋₊ + 1 → orderOf (g : ZMod p) ≠ p - 1 :=
      fun g hg hgX hord => hcon ⟨g, hg, hfl g hgX, hord⟩
    have := h _ (by omega) hXp hno
    linarith
  · obtain ⟨g, hg0, hgp, hord⟩ := exists_primitiveRoot_lt p
    exact ⟨g, hg0, hfl g (by omega), hord⟩

/-- **Main theorem (polynomial in `ω`).** Under GRH, every odd prime `p` has a primitive root
`0 < g ≤ C ω(p-1)^136 (log p)²`, `C = polyC = 1089 (304 · 2^21 · 16^46)²`. -/
theorem leastPrimitiveRoot_le_poly_of_GRH (hGRH : Erdos985.DirichletLNonvanishingRightOfHalf)
    (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) :
    HasPrimitiveRootLE p (polyC * (ω (p - 1) : ℝ) ^ 136 * Real.log p ^ 2) := by
  have hL : 0 ≤ Real.log p := Real.log_nonneg (by exact_mod_cast hp.one_lt.le)
  have hC : 0 ≤ polyC := by rw [polyC_def]; have := c16_pos; positivity
  exact hasPrimitiveRootLE_of_bound p hp _ (by positivity) fun x hx1 hxp hno =>
    le_of_no_primitive_root_lt_poly hGRH p hp hp2 x hx1 hxp hno

/-- `PolyOmegaStatement 136` holds under GRH. -/
theorem polyOmega_of_GRH (hGRH : Erdos985.DirichletLNonvanishingRightOfHalf) :
    PolyOmegaStatement 136 :=
  ⟨polyC, fun p hp hp2 => leastPrimitiveRoot_le_poly_of_GRH hGRH p hp hp2⟩

end Shoup
