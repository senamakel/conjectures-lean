import Shoup.Sieve.Table

/-!
# The error sum: tail and table

* `tail_err`: the primes `ℓ ≤ 2^n` contribute at most `10^{-5}`; on the halving block `h` the
  weight is `≤ 30000 · 4^{h+1}`, the factor excess `≤ 2 R_h`, and `R_h ≤ 10^{-11} 400^{-h}`.
* `err_table_le`: induction over the table classes.
-/

namespace Shoup.Sieve

open Finset Fixed

lemma Rt_le_geom (h : ℕ) : Rt h ≤ 1 / 10 ^ 11 * (1 / 400) ^ h := by
  induction h with
  | zero => simpa using Rt_zero_le
  | succ h ih =>
    have := Rt_succ_le h
    calc Rt (h + 1) ≤ Rt h / 400 := this
      _ ≤ (1 / 10 ^ 11 * (1 / 400) ^ h) / 400 := by gcongr
      _ = _ := by rw [pow_succ]; ring

lemma exp_tail_le (η : ℝ) (h0 : 0 ≤ η) (h1 : η ≤ 1 / 100) :
    Real.exp ((1 + η) * (18 / 25)) ≤ 4 := by
  calc Real.exp ((1 + η) * (18 / 25)) ≤ Real.exp (73 / 100) := Real.exp_le_exp.mpr (by nlinarith)
    _ ≤ 1 / (1 - 73 / 100) := Real.exp_bound_div_one_sub_of_interval (by norm_num) (by norm_num)
    _ ≤ 4 := by norm_num

lemma tailE_le (n h : ℕ) : tailE n h ≤ n := Nat.div_le_self _ _

/-- The factor of the tail design for `ℓ ≤ 2^{n/2^h}`. -/
lemma ratProd_tailDes_le (P : Finset ℕ) (hP : ∀ ℓ ∈ P, ℓ.Prime) (n : ℕ) (hn : 2 ^ 36 ≤ n)
    (h : ℕ) (hh : h ≤ Tn1 n) (ℓ : ℕ) (hℓ : ℓ ≤ 2 ^ tailE n h) :
    ratProd (restr ℓ (desC P n 1 [])) recip ≤ ∏ i ∈ Ico h (Tn1 n), (1 + Rt i) := by
  have hℓn : ℓ ≤ 2 ^ (1 * n) := by
    rw [one_mul]; exact hℓ.trans (Nat.pow_le_pow_right (by norm_num) (tailE_le n h))
  have htop := factor_top_empty P n 1 ℓ hℓn
  have h1 := ratProd_desC_le P hP n hn 1 [] rfl ℓ Dn (by rw [htop, r_Dn])
    _ (ratProd_tail_le P hP n (by omega) h hh ℓ fun _ => hℓ)
  simpa [facProd, r_Dn] using h1

theorem tail_err (P : Finset ℕ) (hP : ∀ ℓ ∈ P, ℓ.Prime) (n : ℕ) (hn : 2 ^ 36 ≤ n) (up : ℕ)
    (hup16 : xq up ≤ 16 * Dn) (hupE : expU (xq up) ≤ 30000 * Dn)
    (hσ : ∑ x ∈ P.filter (fun x => 2 ^ n < x), recip x ≤ r up)
    (Q : Finset ℕ) (hQ : Q ⊆ P) (hQn : ∀ ℓ ∈ Q, ℓ ≤ 2 ^ n) :
    ∑ ℓ ∈ Q, recip ℓ * Wt P recip ℓ * (ratProd (restr ℓ (desC P n 1 [])) recip - 1)
      ≤ 1 / 10 ^ 5 := by
  obtain ⟨hT1, _⟩ := Tn1_facts n (by omega)
  set f : ℕ → ℝ := fun ℓ => recip ℓ * Wt P recip ℓ * (ratProd (restr ℓ (desC P n 1 [])) recip - 1)
  have hE : Real.exp ((1 + 1 / 10 ^ 6) * r up) ≤ 30000 := by
    have := exp_le_expU_of (le_trans le_rfl (xq_ge up)) hup16
    have h2 : r (expU (xq up)) ≤ 30000 := by
      have := r_mono hupE
      have hD : (Dn : ℝ) ≠ 0 := by exact_mod_cast Dn_pos.ne'
      rwa [show r (30000 * Dn) = 30000 by unfold r; push_cast; field_simp] at this
    linarith
  have key : ∀ t j, j + t = (Tn1 n) →
      ∑ x ∈ P.filter (fun x => 2 ^ tailE n j < x), recip x ≤ r up + j * (18 / 25) →
      ∑ ℓ ∈ Q.filter (fun ℓ => ℓ ≤ 2 ^ tailE n j), f ℓ ≤
        ∑ h ∈ Ico j (Tn1 n), (18 / 25 : ℝ) * (30000 * 4 ^ (h + 1)) * (2 * Rt h) := by
    intro t
    induction t with
    | zero =>
      intro j hj _
      rw [add_zero] at hj
      subst hj
      simp only [Finset.Ico_self, Finset.sum_empty]
      refine Finset.sum_nonpos fun ℓ hℓ => ?_
      obtain ⟨hℓQ, hℓT⟩ := Finset.mem_filter.mp hℓ
      have h1 := ratProd_tailDes_le P hP n hn (Tn1 n) le_rfl ℓ hℓT
      simp only [Finset.Ico_self, Finset.prod_empty] at h1
      have hg := (recip_mem (hP ℓ (hQ hℓQ))).1
      have hw := Wt_nonneg P hP ℓ
      exact mul_nonpos_of_nonneg_of_nonpos (mul_nonneg hg hw) (by linarith)
    | succ t ih =>
      intro j hj hσj
      have hjT : j < (Tn1 n) := by omega
      set lo := tailE n (j + 1)
      set hi := tailE n j
      have hlohi : lo ≤ hi := tailE_anti n j hjT
      have hlo : Ubot ≤ lo := by
        have h1 : n / 2 ^ (Tn1 n) ≤ lo :=
          Nat.div_le_div_left (Nat.pow_le_pow_right (by norm_num) (by omega)) (by positivity)
        have h2 : Ubot ≤ n / 2 ^ (Tn1 n) := (Nat.le_div_iff_mul_le (by positivity)).mpr hT1
        omega
      have hlo2 : lo = hi / 2 := by
        simp only [lo, hi, tailE, pow_succ, Nat.div_div_eq_div_mul]
      have hhi2 : hi ≤ 2 * lo + 1 := by rw [hlo2]; omega
      have hloL : 20 ≤ lo := by rw [Ubot_def] at hlo; omega
      -- split off the block
      set Blk := (Q.filter fun ℓ => ℓ ≤ 2 ^ hi).filter fun ℓ => 2 ^ lo < ℓ
      have hrest : (Q.filter fun ℓ => ℓ ≤ 2 ^ hi).filter (fun ℓ => ¬ 2 ^ lo < ℓ) =
          Q.filter fun ℓ => ℓ ≤ 2 ^ lo := by
        have : 2 ^ lo ≤ 2 ^ hi := Nat.pow_le_pow_right (by norm_num) hlohi
        ext x; simp only [Finset.mem_filter, not_lt]
        constructor
        · rintro ⟨⟨h1, _⟩, h3⟩; exact ⟨h1, h3⟩
        · rintro ⟨h1, h3⟩; exact ⟨⟨h1, by omega⟩, h3⟩
      rw [← Finset.sum_filter_add_sum_filter_not _ (fun ℓ => 2 ^ lo < ℓ), hrest]
      have hBP : ∀ x ∈ Blk, x.Prime ∧ 2 ^ lo < x ∧ x ≤ 2 ^ hi := by
        intro x hx
        simp only [Blk, Finset.mem_filter] at hx
        exact ⟨hP x (hQ hx.1.1), hx.2, hx.1.2⟩
      have hsB := sigma_tail_le Blk lo hi hlo hlohi hhi2 hBP
      -- σ above `2^lo`
      have hσblk : ∑ x ∈ P.filter (fun x => 2 ^ lo < x ∧ x ≤ 2 ^ hi), recip x ≤ 18 / 25 :=
        sigma_tail_le _ lo hi hlo hlohi hhi2 fun x hx => by
          simp only [Finset.mem_filter] at hx; exact ⟨hP x hx.1, hx.2⟩
      have hσlo : ∑ x ∈ P.filter (fun x => 2 ^ lo < x), recip x ≤ r up + (j + 1 : ℕ) * (18 / 25) := by
        rw [sigma_split P lo hi hlohi]; push_cast; linarith
      have hσ0 : (0 : ℝ) ≤ r up + (j + 1 : ℕ) * (18 / 25) := by
        have := r_nonneg up; positivity
      -- the weight
      have hη : (1 : ℝ) / 2 ^ lo ≤ 1 / 10 ^ 6 := by
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        have : (10 : ℝ) ^ 6 ≤ 2 ^ lo :=
          calc (10 : ℝ) ^ 6 ≤ 2 ^ 20 := by norm_num
            _ ≤ 2 ^ lo := pow_le_pow_right₀ (by norm_num) hloL
        linarith
      have hW : ∀ ℓ ∈ Blk, Wt P recip ℓ ≤ 30000 * 4 ^ (j + 1) := by
        intro ℓ hℓ
        refine (Wt_le P hP lo (by omega) ℓ (hBP ℓ hℓ).2.1 _ hσlo).trans ?_
        set η : ℝ := 1 / 2 ^ lo
        have hη0 : 0 ≤ η := by positivity
        have e : (1 + η) * (r up + (j + 1 : ℕ) * (18 / 25)) =
            (1 + η) * r up + (j + 1 : ℕ) * ((1 + η) * (18 / 25)) := by ring
        rw [e, Real.exp_add, Real.exp_nat_mul]
        have h1 : Real.exp ((1 + η) * r up) ≤ 30000 :=
          le_trans (Real.exp_le_exp.mpr (by have := r_nonneg up; nlinarith)) hE
        have h2 := exp_tail_le η hη0 (by linarith)
        have h3 : Real.exp ((1 + η) * (18 / 25)) ^ (j + 1) ≤ 4 ^ (j + 1) :=
          pow_le_pow_left₀ (Real.exp_pos _).le h2 _
        exact mul_le_mul h1 h3 (by positivity) (by norm_num)
      have hR : ∀ ℓ ∈ Blk, ratProd (restr ℓ (desC P n 1 [])) recip - 1 ≤ 2 * Rt j := by
        intro ℓ hℓ
        have h1 := ratProd_tailDes_le P hP n hn j hjT.le ℓ (hBP ℓ hℓ).2.2
        have h2 := prod_R_le (Tn1 n) j hjT.le
        linarith
      have hblk := class_err_le P hP Blk (fun x hx => hQ (by
          simp only [Blk, Finset.mem_filter] at hx; exact hx.1.1))
        (desC P n 1 []) (18 / 25) (30000 * 4 ^ (j + 1)) (2 * Rt j)
        (by have := Rt_nonneg j; linarith) (by positivity) hsB hW hR
      have hih := ih (j + 1) (by omega) (by push_cast at hσlo ⊢; linarith)
      rw [Finset.sum_eq_sum_Ico_succ_bot hjT]
      exact add_le_add hblk hih
  have hall := key (Tn1 n) 0 (by ring) (by simpa [tailE] using hσ)
  have hQ0 : Q.filter (fun ℓ => ℓ ≤ 2 ^ tailE n 0) = Q := by
    apply Finset.filter_true_of_mem
    intro ℓ h; simpa [tailE] using hQn ℓ h
  rw [hQ0] at hall
  refine hall.trans ?_
  have hterm : ∀ h ∈ Ico 0 (Tn1 n), (18 / 25 : ℝ) * (30000 * 4 ^ (h + 1)) * (2 * Rt h) ≤
      (18 / 25 * 30000 * 4 * 2 / 10 ^ 11 : ℝ) * (1 / 100) ^ h := by
    intro h _
    have := Rt_le_geom h
    have e : (4 : ℝ) ^ (h + 1) * (1 / 400) ^ h = 4 * (1 / 100) ^ h := by
      rw [pow_succ, mul_comm ((4 : ℝ) ^ h) 4, mul_assoc, ← mul_pow]; norm_num
    calc (18 / 25 : ℝ) * (30000 * 4 ^ (h + 1)) * (2 * Rt h)
        ≤ (18 / 25 : ℝ) * (30000 * 4 ^ (h + 1)) * (2 * (1 / 10 ^ 11 * (1 / 400) ^ h)) := by
          gcongr
      _ = (18 / 25 * 30000 * 2 / 10 ^ 11 : ℝ) * (4 ^ (h + 1) * (1 / 400) ^ h) := by ring
      _ = _ := by rw [e]; ring
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [← Finset.mul_sum, ← Finset.range_eq_Ico]
  have hg := geom_sum_mul (1 / 100 : ℝ) (Tn1 n)
  have : (0 : ℝ) ≤ (1 / 100) ^ (Tn1 n) := by positivity
  have hs : ∑ i ∈ range (Tn1 n), (1 / 100 : ℝ) ^ i ≤ 100 / 99 := by nlinarith
  calc (18 / 25 * 30000 * 4 * 2 / 10 ^ 11 : ℝ) * ∑ i ∈ range (Tn1 n), (1 / 100 : ℝ) ^ i
      ≤ (18 / 25 * 30000 * 4 * 2 / 10 ^ 11 : ℝ) * (100 / 99) := by gcongr
    _ ≤ 1 / 10 ^ 5 := by norm_num

lemma r_TAILF : 1 + 1 / 10 ^ 9 ≤ r TAILF := by
  unfold TAILF
  rw [r_add, r_Dn]
  have := cdiv_ge Dn (10 ^ 9) (by norm_num)
  rw [r_Dn] at this
  push_cast at this
  linarith

lemma tail_le_TAILF (P : Finset ℕ) (hP : ∀ ℓ ∈ P, ℓ.Prime) (n : ℕ) (hn : 2 ^ 36 ≤ n) (ℓ : ℕ) :
    ratProd (restr ℓ (tailPart P n)) recip ≤ r TAILF := by
  have h1 := ratProd_tail_le P hP n (by omega) 0 (Nat.zero_le _) ℓ (fun h => absurd h (lt_irrefl 0))
  have h2 := prod_R_le (Tn1 n) 0 (Nat.zero_le _)
  have h3 := Rt_zero_le
  have h4 := r_TAILF
  linarith

lemma r_sub_ge (x : ℕ) : r x - 1 ≤ r (x - Dn) := by
  by_cases h : Dn ≤ x
  · rw [r_sub h, r_Dn]
  · push Not at h
    rw [Nat.sub_eq_zero_of_le h.le]
    have := r_mono h.le
    rw [r_Dn] at this
    have : r 0 = 0 := by simp [r]
    linarith

end Shoup.Sieve
