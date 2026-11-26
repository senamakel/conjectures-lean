import Shoup.Sieve.Design

/-!
# Factor bounds for the designs

For `ℓ` and a design `desC P n hi rs`, the product `ratProd (restr ℓ ·)` of the factors `U/A`
of the blocks restricted to the primes below `ℓ` is bounded by

* `∏_{h ∈ [h₀, T)} (1 + R_h)` on the tail, when `ℓ ≤ 2^{n/2^{h₀}}` (`ratProd_tail_le`), with
  `R_h = (18/25)^{2h+13}/(2h+13)! · 4`; this is `≤ 1 + 2 R_{h₀}` (`prod_R_le`);
* `facProd rs / D` on the rows (`ratProd_cust_le`);
* `1` on the top block when `ℓ ≤ 2^{hi n}`, and `expU (xq up) / D` when
  `Σ_{ℓ ∈ P, ℓ > 2^{hi n}} 1/ℓ ≤ up / D` (`factor_top_le`).
-/

namespace Shoup.Sieve

open Finset Fixed

/-! ### `ratProd` and restriction -/

lemma restr_cons (ℓ : ℕ) (b : Block) (L : List Block) :
    restr ℓ (b :: L) = (b.1.filter (· < ℓ), b.2) :: restr ℓ L := rfl

lemma restr_append (ℓ : ℕ) (L₁ L₂ : List Block) :
    restr ℓ (L₁ ++ L₂) = restr ℓ L₁ ++ restr ℓ L₂ := List.map_append

lemma ratProd_cons (b : Block) (L : List Block) (y : ℕ → ℝ) :
    ratProd (b :: L) y = Ub b y / Ab b y * ratProd L y := rfl

lemma ratProd_restr_map_range (ℓ : ℕ) (g : ℕ → Block) (t : ℕ) (y : ℕ → ℝ) :
    ratProd (restr ℓ ((List.range t).map g)) y =
      ∏ i ∈ range t, Ub ((g i).1.filter (· < ℓ), (g i).2) y /
        Ab ((g i).1.filter (· < ℓ), (g i).2) y := by
  induction t with
  | zero => simp [restr, ratProd]
  | succ t ih =>
    rw [List.range_succ, List.map_append, restr_append, ratProd_append, ih,
      Finset.prod_range_succ]
    simp [restr, ratProd]

lemma recip_prime_mem {ℓ : ℕ} (h : ℓ.Prime) : 0 ≤ recip ℓ ∧ recip ℓ ≤ 1 / 2 := recip_mem h

lemma factor_nonneg (b : Block) (hb : ∀ ℓ ∈ b.1, ℓ.Prime) : 0 ≤ Ub b recip / Ab b recip := by
  have hy : ∀ ℓ ∈ b.1, 0 ≤ recip ℓ ∧ recip ℓ ≤ 1 / 2 := fun ℓ h => recip_mem (hb ℓ h)
  have hy' : ∀ ℓ ∈ b.1, 0 ≤ recip ℓ ∧ recip ℓ ≤ 1 :=
    fun ℓ h => ⟨(hy ℓ h).1, by linarith [(hy ℓ h).2]⟩
  obtain ⟨a0, aU, _⟩ := block_bounds recip b hy'
  exact div_nonneg (a0.trans aU) (Ab_pos recip b hy).le

lemma factor_eq_one_of_empty (B : Finset ℕ) (k ℓ : ℕ) (h : ∀ x ∈ B, ℓ ≤ x) :
    Ub (B.filter (· < ℓ), k) recip / Ab (B.filter (· < ℓ), k) recip = 1 := by
  have : B.filter (· < ℓ) = ∅ := by
    ext x; simp only [Finset.mem_filter, Finset.notMem_empty, iff_false, not_and, not_lt]
    exact h x
  rw [this]; exact factor_empty k recip

/-! ### The tail -/

lemma Tn1_facts (n : ℕ) (hn : 2 ^ 23 ≤ n) :
    Ubot * 2 ^ Tn1 n ≤ n ∧ n < 2 * Ubot * 2 ^ Tn1 n := by
  have hU : 0 < Ubot := by rw [Ubot_def]; positivity
  set q := n / Ubot with hq
  have hq0 : q ≠ 0 := by
    rw [hq]; apply Nat.div_ne_zero_iff.mpr
    rw [Ubot_def]; omega
  have h1 : 2 ^ Tn1 n ≤ q := Nat.pow_log_le_self 2 hq0
  have h2 : q < 2 ^ (Tn1 n + 1) := Nat.lt_pow_succ_log_self (by norm_num) q
  have h3 : q * Ubot ≤ n := Nat.div_mul_le_self _ _
  have h4 : n < q * Ubot + Ubot := Nat.lt_div_mul_add hU
  constructor
  · calc Ubot * 2 ^ Tn1 n ≤ Ubot * q := Nat.mul_le_mul_left _ h1
      _ = q * Ubot := by ring
      _ ≤ n := h3
  · have : q + 1 ≤ 2 ^ (Tn1 n + 1) := h2
    calc n < q * Ubot + Ubot := h4
      _ = (q + 1) * Ubot := by ring
      _ ≤ 2 ^ (Tn1 n + 1) * Ubot := Nat.mul_le_mul_right _ this
      _ = 2 * Ubot * 2 ^ Tn1 n := by ring

/-- `R_h = (18/25)^{2h+13}/(2h+13)! · 4`. -/
noncomputable def Rt (h : ℕ) : ℝ := (18 / 25 : ℝ) ^ (2 * h + 13) / (2 * h + 13).factorial * 4

lemma Rt_nonneg (h : ℕ) : 0 ≤ Rt h := by unfold Rt; positivity

lemma Rt_succ_le (h : ℕ) : Rt (h + 1) ≤ Rt h / 400 := by
  unfold Rt
  have hf : ((2 * (h + 1) + 13).factorial : ℝ) =
      (2 * h + 15) * (2 * h + 14) * (2 * h + 13).factorial := by
    rw [show 2 * (h + 1) + 13 = (2 * h + 13) + 1 + 1 by ring, Nat.factorial_succ,
      Nat.factorial_succ]
    push_cast; ring
  have hp : (18 / 25 : ℝ) ^ (2 * (h + 1) + 13) = (18 / 25) ^ (2 * h + 13) * (18 / 25) ^ 2 := by
    rw [← pow_add]; congr 1
  rw [hf, hp]
  have hF : (0 : ℝ) < (2 * h + 13).factorial := by exact_mod_cast Nat.factorial_pos _
  have hX : (0 : ℝ) ≤ (18 / 25 : ℝ) ^ (2 * h + 13) := by positivity
  have hh : (0 : ℝ) ≤ h := Nat.cast_nonneg h
  have hq : (0 : ℝ) < (2 * h + 15) * (2 * h + 14) := by positivity
  have key : (18 / 25 : ℝ) ^ (2 * h + 13) * (18 / 25) ^ 2 /
      ((2 * h + 15) * (2 * h + 14) * (2 * h + 13).factorial) * 4 =
      ((18 / 25 : ℝ) ^ (2 * h + 13) / (2 * h + 13).factorial * 4) *
        ((18 / 25) ^ 2 / ((2 * h + 15) * (2 * h + 14))) := by
    field_simp
  rw [key]
  have hr : (18 / 25 : ℝ) ^ 2 / ((2 * h + 15) * (2 * h + 14)) ≤ 1 / 400 := by
    rw [div_le_div_iff₀ hq (by norm_num)]; nlinarith
  have h0 : (0 : ℝ) ≤ (18 / 25 : ℝ) ^ (2 * h + 13) / (2 * h + 13).factorial * 4 := by positivity
  calc _ ≤ ((18 / 25 : ℝ) ^ (2 * h + 13) / (2 * h + 13).factorial * 4) * (1 / 400) :=
        mul_le_mul_of_nonneg_left hr h0
    _ = _ := by ring

lemma Rt_zero_le : Rt 0 ≤ 1 / 10 ^ 11 := by
  unfold Rt; norm_num [Nat.factorial]

lemma Rt_le_one (h : ℕ) : Rt h ≤ 1 := by
  induction h with
  | zero => have := Rt_zero_le; linarith
  | succ h ih => have := Rt_succ_le h; have := Rt_nonneg h; linarith

/-- `∏_{h ∈ [j, T)} (1 + R_h) ≤ 1 + 2 R_j`. -/
lemma prod_R_le (T : ℕ) : ∀ j ≤ T, ∏ h ∈ Ico j T, (1 + Rt h) ≤ 1 + 2 * Rt j := by
  intro j hj
  obtain ⟨t, rfl⟩ : ∃ t, T = j + t := ⟨T - j, by omega⟩
  clear hj
  induction t generalizing j with
  | zero => simp; linarith [Rt_nonneg j]
  | succ t ih =>
    rw [Finset.prod_eq_prod_Ico_succ_bot (by omega)]
    have h1 := ih (j + 1)
    rw [show j + 1 + t = j + (t + 1) by ring] at h1
    have h2 := Rt_succ_le j
    have h3 := Rt_nonneg j
    have h4 := Rt_le_one j
    have h5 := Rt_nonneg (j + 1)
    have hP : 0 ≤ ∏ h ∈ Ico (j + 1) (j + (t + 1)), (1 + Rt h) :=
      Finset.prod_nonneg fun h _ => by linarith [Rt_nonneg h]
    calc (1 + Rt j) * ∏ h ∈ Ico (j + 1) (j + (t + 1)), (1 + Rt h)
        ≤ (1 + Rt j) * (1 + 2 * Rt (j + 1)) := mul_le_mul_of_nonneg_left h1 (by linarith)
      _ ≤ 1 + 2 * Rt j := by nlinarith

lemma tail_block_mem {P : Finset ℕ} {n h ℓ : ℕ}
    (hℓ : ℓ ∈ (midT P (tailE n) tailLev h).1) :
    ℓ ∈ P ∧ 2 ^ tailE n (h + 1) < ℓ ∧ ℓ ≤ 2 ^ tailE n h := by
  simp only [midT, Finset.mem_filter] at hℓ; exact ⟨hℓ.1, hℓ.2⟩

/-- The tail factor for `ℓ ≤ 2^{n / 2^{h₀}}`. -/
theorem ratProd_tail_le (P : Finset ℕ) (hP : ∀ ℓ ∈ P, ℓ.Prime) (n : ℕ) (hn : 2 ^ 23 ≤ n)
    (h₀ : ℕ) (hh₀ : h₀ ≤ Tn1 n) (ℓ : ℕ) (hℓ : 0 < h₀ → ℓ ≤ 2 ^ tailE n h₀) :
    ratProd (restr ℓ (tailPart P n)) recip ≤ ∏ h ∈ Ico h₀ (Tn1 n), (1 + Rt h) := by
  obtain ⟨hT1, hT2⟩ := Tn1_facts n hn
  unfold tailPart
  rw [restr_cons, ratProd_cons, ratProd_restr_map_range]
  -- the bottom block is exact
  have hbot : Ub (((botT P (tailE n) (Tn1 n) kbot).1).filter (· < ℓ), kbot) recip /
      Ab (((botT P (tailE n) (Tn1 n) kbot).1).filter (· < ℓ), kbot) recip = 1 := by
    apply factor_exact
    · intro x hx
      exact recip_mem (hP x (Finset.mem_filter.mp (Finset.mem_filter.mp hx).1).1)
    · have hK : tailE n (Tn1 n) < 2 * Ubot := by
        unfold tailE
        exact (Nat.div_lt_iff_lt_mul (by positivity)).mpr (by linarith)
      have hsub : ((botT P (tailE n) (Tn1 n) kbot).1).filter (· < ℓ) ⊆
          Finset.Icc 1 (2 ^ tailE n (Tn1 n)) := by
        intro x hx
        simp only [botT, Finset.mem_filter] at hx
        exact Finset.mem_Icc.mpr ⟨(hP x hx.1.1).one_lt.le, hx.1.2⟩
      have := Finset.card_le_card hsub
      rw [Nat.card_Icc] at this
      have : 2 ^ tailE n (Tn1 n) ≤ 2 ^ (2 * Ubot) := Nat.pow_le_pow_right (by norm_num) hK.le
      have hk : kbot = 2 ^ (2 * Ubot) := rfl
      omega
  have hbot' : (botT P (tailE n) (Tn1 n) kbot).2 = kbot := rfl
  rw [show (((botT P (tailE n) (Tn1 n) kbot).1).filter (· < ℓ), (botT P (tailE n) (Tn1 n) kbot).2) =
      (((botT P (tailE n) (Tn1 n) kbot).1).filter (· < ℓ), kbot) from rfl, hbot, one_mul]
  rw [← Finset.prod_range_mul_prod_Ico _ hh₀]
  have hlow : ∏ i ∈ range h₀, Ub (((midT P (tailE n) tailLev i).1).filter (· < ℓ),
      (midT P (tailE n) tailLev i).2) recip / Ab (((midT P (tailE n) tailLev i).1).filter (· < ℓ),
      (midT P (tailE n) tailLev i).2) recip = 1 := by
    refine Finset.prod_eq_one fun i hi => ?_
    apply factor_eq_one_of_empty
    intro x hx
    have := (tail_block_mem hx).2.1
    have hi' := Finset.mem_range.mp hi
    have := hℓ (by omega)
    have : 2 ^ tailE n h₀ ≤ 2 ^ tailE n (i + 1) :=
      pow_e_anti (tailE_anti n) (show i + 1 ≤ h₀ by omega) hh₀
    omega
  rw [hlow, one_mul]
  refine Finset.prod_le_prod₀ (fun i _ => factor_nonneg _ fun x hx =>
    hP x (tail_block_mem (Finset.mem_filter.mp hx).1).1) fun i hi => ?_
  have hiT := (Finset.mem_Ico.mp hi).2
  set lo := tailE n (i + 1)
  set hi' := tailE n i
  have hlo : Ubot ≤ lo := by
    have h1 : n / 2 ^ Tn1 n ≤ lo :=
      Nat.div_le_div_left (Nat.pow_le_pow_right (by norm_num) (by omega)) (by positivity)
    have h2 : Ubot ≤ n / 2 ^ Tn1 n := (Nat.le_div_iff_mul_le (by positivity)).mpr hT1
    omega
  have hlo2 : lo = hi' / 2 := by
    simp only [lo, hi', tailE, pow_succ, Nat.div_div_eq_div_mul]
  have hlh : lo ≤ hi' := by rw [hlo2]; exact Nat.div_le_self _ _
  have hhi : hi' ≤ 2 * lo + 1 := by rw [hlo2]; omega
  set B := ((midT P (tailE n) tailLev i).1).filter (· < ℓ)
  have hB : ∀ x ∈ B, x.Prime ∧ 2 ^ lo < x ∧ x ≤ 2 ^ hi' := by
    intro x hx
    obtain ⟨h1, h2, h3⟩ := tail_block_mem (Finset.mem_filter.mp hx).1
    exact ⟨hP x h1, h2, h3⟩
  have hs := sigma_tail_le B lo hi' hlo hlh hhi hB
  have hlo7 : 7 ≤ lo := by rw [Ubot_def] at hlo; omega
  have hη : (1 : ℝ) / 2 ^ lo ≤ 1 / 100 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    have : (100 : ℝ) ≤ 2 ^ lo :=
      calc (100 : ℝ) ≤ 2 ^ 7 := by norm_num
        _ ≤ 2 ^ lo := pow_le_pow_right₀ (by norm_num) hlo7
    linarith
  have hy : ∀ x ∈ B, 0 ≤ recip x ∧ recip x ≤ 1 / 2 ^ lo := by
    intro x hx
    have : (2 : ℝ) ^ lo < x := by exact_mod_cast (hB x hx).2.1
    exact ⟨by unfold recip; positivity, one_div_le_one_div_of_le (by positivity) this.le⟩
  have hf := factor_le B (tailLev i) recip (by linarith) hy
  have hσ0 := sum_recip_nonneg B
  have hexp : Real.exp ((1 + 1 / 2 ^ lo) * ∑ x ∈ B, recip x) ≤ 4 := by
    have hx : (1 + 1 / 2 ^ lo) * ∑ x ∈ B, recip x ≤ 73 / 100 := by
      have : (0 : ℝ) ≤ 1 / 2 ^ lo := by positivity
      nlinarith
    calc Real.exp ((1 + 1 / 2 ^ lo) * ∑ x ∈ B, recip x) ≤ Real.exp (73 / 100) :=
          Real.exp_le_exp.mpr hx
      _ ≤ 1 / (1 - 73 / 100) :=
          Real.exp_bound_div_one_sub_of_interval (by norm_num) (by norm_num)
      _ ≤ 4 := by norm_num
  have hlev : 2 * tailLev i + 1 = 2 * i + 13 := by simp [tailLev]; ring
  have hk : (midT P (tailE n) tailLev i).2 = tailLev i := rfl
  rw [hk]
  refine hf.trans ?_
  rw [hlev]
  unfold Rt
  have hf0 : (0 : ℝ) < (2 * i + 13).factorial := by exact_mod_cast Nat.factorial_pos _
  have hpow := pow_le_pow_left₀ hσ0 hs (2 * i + 13)
  have := mul_le_mul (div_le_div_of_nonneg_right hpow hf0.le) hexp (Real.exp_pos _).le
    (by positivity)
  linarith

/-! ### The rows -/

/-- Product of the row factors. -/
def facProd : List Row → ℕ
  | [] => Dn
  | x :: rs => mulU (facN x.1 x.2.1 x.2.2.1 x.2.2.2) (facProd rs)

theorem ratProd_cust_le (P : Finset ℕ) (hP : ∀ ℓ ∈ P, ℓ.Prime) (n : ℕ) (hn : 2 ^ 36 ≤ n)
    (ℓ : ℕ) : ∀ (rs : List Row) (t : ℕ), chainOK t rs = true →
      ratProd (restr ℓ (custBlocks P n rs)) recip ≤ r (facProd rs) := by
  intro rs
  induction rs with
  | nil => intro t _; simp [custBlocks, restr, ratProd, facProd, r_Dn]
  | cons x rs ih =>
    intro t ht
    rcases x with ⟨a, b, k, c⟩
    simp only [chainOK, Bool.and_eq_true, beq_iff_eq] at ht
    obtain ⟨⟨_, hrow⟩, hch⟩ := ht
    have h1 := ih b hch
    show Ub ((P.filter fun ℓ => 2 ^ (b * n) < ℓ ∧ ℓ ≤ 2 ^ (a * n)).filter (· < ℓ), k) recip /
        Ab ((P.filter fun ℓ => 2 ^ (b * n) < ℓ ∧ ℓ ≤ 2 ^ (a * n)).filter (· < ℓ), k) recip *
        ratProd (restr ℓ (custBlocks P n rs)) recip ≤ r (facProd ((a, b, k, c) :: rs))
    have hB : ∀ x ∈ (P.filter fun ℓ => 2 ^ (b * n) < ℓ ∧ ℓ ≤ 2 ^ (a * n)).filter (· < ℓ),
        x.Prime ∧ 2 ^ (b * n) < x ∧ x ≤ 2 ^ (a * n) := by
      intro x hx
      have := (Finset.mem_filter.mp (Finset.mem_filter.mp hx).1)
      exact ⟨hP x this.1, this.2⟩
    have h2 := factor_le_facN _ hB k c hn hrow
    have h0 := factor_nonneg (((P.filter fun ℓ => 2 ^ (b * n) < ℓ ∧ ℓ ≤ 2 ^ (a * n)).filter
      (· < ℓ)), k) fun x hx => (hB x hx).1
    have h3 : 0 ≤ ratProd (restr ℓ (custBlocks P n rs)) recip := by
      apply ratProd_nonneg
      intro x hx
      rw [supp_restr] at hx
      have := (Finset.mem_filter.mp hx).1
      rw [((cust_spec P n rs b hch).2 x)] at this
      exact recip_mem (hP x this.1)
    exact mulU_ge_of h0 h3 h2 h1

/-! ### The top block -/

lemma factor_top_empty (P : Finset ℕ) (n hi ℓ : ℕ) (hℓ : ℓ ≤ 2 ^ (hi * n)) :
    Ub ((P.filter fun x => 2 ^ (hi * n) < x).filter (· < ℓ), 0) recip /
      Ab ((P.filter fun x => 2 ^ (hi * n) < x).filter (· < ℓ), 0) recip = 1 := by
  apply factor_eq_one_of_empty
  intro x hx
  have := (Finset.mem_filter.mp hx).2
  omega

lemma factor_top_le (P : Finset ℕ) (hP : ∀ ℓ ∈ P, ℓ.Prime) (n hi ℓ up : ℕ) (hhi : 1 ≤ hi)
    (hn : 2 ^ 20 ≤ n) (hσ : ∑ x ∈ P.filter (fun x => 2 ^ (hi * n) < x), recip x ≤ r up)
    (hup : xq up ≤ 16 * Dn) :
    Ub ((P.filter fun x => 2 ^ (hi * n) < x).filter (· < ℓ), 0) recip /
      Ab ((P.filter fun x => 2 ^ (hi * n) < x).filter (· < ℓ), 0) recip ≤ r (expU (xq up)) := by
  set B := (P.filter fun x => 2 ^ (hi * n) < x).filter (· < ℓ)
  set η : ℝ := 1 / 2 ^ (hi * n)
  have hη6 : η ≤ 1 / 10 ^ 6 := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have : (10 : ℝ) ^ 6 ≤ 2 ^ (hi * n) :=
      calc (10 : ℝ) ^ 6 ≤ 2 ^ 20 := by norm_num
        _ ≤ 2 ^ (hi * n) := pow_le_pow_right₀ (by norm_num) (by nlinarith)
    linarith
  have hy : ∀ x ∈ B, 0 ≤ recip x ∧ recip x ≤ η := by
    intro x hx
    have : (2 : ℝ) ^ (hi * n) < x := by
      exact_mod_cast (Finset.mem_filter.mp (Finset.mem_filter.mp hx).1).2
    exact ⟨by unfold recip; positivity, one_div_le_one_div_of_le (by positivity) this.le⟩
  have hf := factor_zero_le B recip (by linarith) hy
  have hsub : ∑ x ∈ B, recip x ≤ r up :=
    le_trans (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      fun x _ _ => by unfold recip; positivity) hσ
  have hB0 := sum_recip_nonneg B
  have hη0 : 0 ≤ η := by positivity
  have hx : (1 + η) * ∑ x ∈ B, recip x ≤ r (xq up) := by
    refine le_trans ?_ (xq_ge up)
    have := r_nonneg up
    nlinarith
  exact hf.trans (exp_le_expU_of hx hup)

/-! ### A whole design -/

theorem ratProd_desC_le (P : Finset ℕ) (hP : ∀ ℓ ∈ P, ℓ.Prime) (n : ℕ) (hn : 2 ^ 36 ≤ n)
    (hi : ℕ) (rs : List Row) (hch : chainOK hi rs = true) (ℓ : ℕ) (topF : ℕ)
    (htop : Ub ((P.filter fun x => 2 ^ (hi * n) < x).filter (· < ℓ), 0) recip /
      Ab ((P.filter fun x => 2 ^ (hi * n) < x).filter (· < ℓ), 0) recip ≤ r topF)
    (tailB : ℝ) (htail : ratProd (restr ℓ (tailPart P n)) recip ≤ tailB) :
    ratProd (restr ℓ (desC P n hi rs)) recip ≤ r topF * r (facProd rs) * tailB := by
  unfold desC
  rw [restr_cons, ratProd_cons, restr_append, ratProd_append]
  have hc := ratProd_cust_le P hP n hn ℓ rs hi hch
  have h0 := factor_nonneg (((P.filter fun x => 2 ^ (hi * n) < x).filter (· < ℓ)), 0)
    fun x hx => hP x (Finset.mem_filter.mp (Finset.mem_filter.mp hx).1).1
  have hsupp : ∀ L : List Block, supp L ⊆ P → 0 ≤ ratProd (restr ℓ L) recip := by
    intro L hL
    apply ratProd_nonneg
    intro x hx
    rw [supp_restr] at hx
    exact recip_mem (hP x (hL (Finset.mem_filter.mp hx).1))
  have hc0 := hsupp (custBlocks P n rs) fun x hx =>
    ((cust_spec P n rs hi hch).2 x |>.mp hx).1
  have ht0 := hsupp (tailPart P n) fun x hx => (((tailPart_spec P n).2 x).mp hx).1
  have hF0 := r_nonneg (facProd rs)
  calc _ = (Ub ((P.filter fun x => 2 ^ (hi * n) < x).filter (· < ℓ), 0) recip /
        Ab ((P.filter fun x => 2 ^ (hi * n) < x).filter (· < ℓ), 0) recip) *
        (ratProd (restr ℓ (custBlocks P n rs)) recip * ratProd (restr ℓ (tailPart P n)) recip) := rfl
    _ ≤ r topF * (r (facProd rs) * tailB) := by
        apply mul_le_mul htop (mul_le_mul hc htail ht0 hF0) (mul_nonneg hc0 ht0)
        exact h0.trans htop
    _ = _ := by ring

end Shoup.Sieve
