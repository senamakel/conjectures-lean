import Shoup.Sieve.TableErr

namespace Shoup.Sieve

open Finset Fixed

theorem err_table_le (P : Finset ℕ) (hP : ∀ ℓ ∈ P, ℓ.Prime) (n : ℕ) (hn : 2 ^ 36 ≤ n) (S : ℕ) :
    ∀ (tab : List Cls) (first : Bool) (up t : ℕ) (Q : Finset ℕ),
      tableOK S first up t tab = true → Q ⊆ P → 1 ≤ t →
      (first = false → ∀ ℓ ∈ Q, ℓ ≤ 2 ^ (t * n)) →
      ∑ x ∈ P.filter (fun x => 2 ^ (t * n) < x), recip x ≤ r up →
      ∑ ℓ ∈ Q, recip ℓ * Wt P recip ℓ *
          (ratProd (restr ℓ (pick (desC P n 1 []) ℓ (custList P n tab))) recip - 1)
        ≤ r (errSum first up tab) + 1 / 10 ^ 5 := by
  intro tab
  induction tab with
  | nil =>
    intro first up t Q hok hQ ht hQt hσ
    simp only [tableOK, Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq, decide_eq_true_eq] at hok
    obtain ⟨⟨⟨hf, ht1⟩, h16⟩, hE⟩ := hok
    subst ht1
    have hQn : ∀ ℓ ∈ Q, ℓ ≤ 2 ^ n := fun ℓ h => by simpa using hQt hf ℓ h
    have := tail_err P hP n hn up h16 hE (by simpa using hσ) Q hQ hQn
    simp only [pick, custList, errSum]
    have : r 0 = 0 := by simp [r]
    linarith
  | cons C rest ih =>
    intro first up t Q hok hQ ht hQt hσ
    simp only [tableOK, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hok
    obtain ⟨⟨⟨⟨⟨⟨⟨hhi, hrow⟩, hch⟩, h16⟩, h16'⟩, _⟩, _⟩, hrest⟩ := hok
    subst hhi
    set s := sigq C.hi C.lo C.cl
    have hrow' := hrow
    simp only [rowOK, Bool.and_eq_true, decide_eq_true_eq] at hrow'
    obtain ⟨⟨⟨⟨hlo0, hlohi⟩, _⟩, _⟩, _⟩ := hrow'
    have hLH : C.lo * n ≤ C.hi * n := Nat.mul_le_mul_right n hlohi.le
    -- σ bounds
    have hσmid : ∑ x ∈ P.filter (fun x => 2 ^ (C.lo * n) < x ∧ x ≤ 2 ^ (C.hi * n)), recip x ≤ r s :=
      sigma_le_sigq _ (fun x hx => hP x (Finset.mem_filter.mp hx).1) 0 C.cl
        (fun x hx => (Finset.mem_filter.mp hx).2) hn hrow
    have hσlo : ∑ x ∈ P.filter (fun x => 2 ^ (C.lo * n) < x), recip x ≤ r (up + s) := by
      rw [sigma_split P _ _ hLH, r_add]; linarith
    -- split `Q`
    rw [← Finset.sum_filter_add_sum_filter_not Q (fun ℓ => 2 ^ (C.lo * n) < ℓ)]
    simp only [errSum, r_add]
    have hhiQ : ∑ ℓ ∈ Q.filter (fun ℓ => 2 ^ (C.lo * n) < ℓ), recip ℓ * Wt P recip ℓ *
        (ratProd (restr ℓ (pick (desC P n 1 []) ℓ (custList P n (C :: rest)))) recip - 1) =
        ∑ ℓ ∈ Q.filter (fun ℓ => 2 ^ (C.lo * n) < ℓ), recip ℓ * Wt P recip ℓ *
        (ratProd (restr ℓ (desC P n C.hi C.des)) recip - 1) := by
      refine Finset.sum_congr rfl fun ℓ hℓ => ?_
      have h := (Finset.mem_filter.mp hℓ).2
      simp only [custList, pick, if_pos h]
    have hloQ : ∑ ℓ ∈ Q.filter (fun ℓ => ¬ 2 ^ (C.lo * n) < ℓ), recip ℓ * Wt P recip ℓ *
        (ratProd (restr ℓ (pick (desC P n 1 []) ℓ (custList P n (C :: rest)))) recip - 1) =
        ∑ ℓ ∈ Q.filter (fun ℓ => ¬ 2 ^ (C.lo * n) < ℓ), recip ℓ * Wt P recip ℓ *
        (ratProd (restr ℓ (pick (desC P n 1 []) ℓ (custList P n rest))) recip - 1) := by
      refine Finset.sum_congr rfl fun ℓ hℓ => ?_
      have h := (Finset.mem_filter.mp hℓ).2
      simp only [custList, pick, if_neg h]
    rw [hhiQ, hloQ]
    have hrecQ := ih false (up + s) C.lo (Q.filter fun ℓ => ¬ 2 ^ (C.lo * n) < ℓ) hrest
      ((Finset.filter_subset _ _).trans hQ) hlo0 (fun _ ℓ hℓ => by
        have := (Finset.mem_filter.mp hℓ).2; omega) hσlo
    -- the class itself
    set Qh := Q.filter (fun ℓ => 2 ^ (C.lo * n) < ℓ)
    have hQhP : Qh ⊆ P := (Finset.filter_subset _ _).trans hQ
    have hs : ∑ ℓ ∈ Qh, recip ℓ ≤ r (s + if first then up else 0) := by
      cases first with
      | true =>
        simp only [if_true, r_add]
        have : ∑ ℓ ∈ Qh, recip ℓ ≤ ∑ x ∈ P.filter (fun x => 2 ^ (C.lo * n) < x), recip x :=
          sum_recip_mono fun x hx => by
            simp only [Qh, Finset.mem_filter] at hx ⊢; exact ⟨hQ hx.1, hx.2⟩
        rw [r_add] at hσlo; linarith
      | false =>
        simp only [Bool.false_eq_true, if_false, add_zero]
        refine le_trans (sum_recip_mono fun x hx => ?_) hσmid
        simp only [Qh, Finset.mem_filter] at hx ⊢
        exact ⟨hQ hx.1, hx.2, hQt rfl x hx.1⟩
    have hLn : 2 ≤ C.lo * n := by nlinarith
    have hW : ∀ ℓ ∈ Qh, Wt P recip ℓ ≤ r (expU (xq (up + s))) := by
      intro ℓ hℓ
      refine (Wt_le P hP (C.lo * n) hLn ℓ (Finset.mem_filter.mp hℓ).2 _ hσlo).trans ?_
      have hη : (1 : ℝ) / 2 ^ (C.lo * n) ≤ 1 / 10 ^ 6 := by
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        have : (10 : ℝ) ^ 6 ≤ 2 ^ (C.lo * n) :=
          calc (10 : ℝ) ^ 6 ≤ 2 ^ 20 := by norm_num
            _ ≤ 2 ^ (C.lo * n) := pow_le_pow_right₀ (by norm_num) (by nlinarith)
        linarith
      refine exp_le_expU_of (le_trans ?_ (xq_ge (up + s))) h16'
      have := r_nonneg (up + s)
      have : (0 : ℝ) ≤ 1 / 2 ^ (C.lo * n) := by positivity
      nlinarith
    have htop : ∀ ℓ ∈ Qh, Ub ((P.filter fun x => 2 ^ (C.hi * n) < x).filter (· < ℓ), 0) recip /
        Ab ((P.filter fun x => 2 ^ (C.hi * n) < x).filter (· < ℓ), 0) recip ≤
          r (if first then expU (xq up) else Dn) := by
      intro ℓ hℓ
      cases first with
      | true =>
        rw [if_pos rfl]
        exact factor_top_le P hP n C.hi ℓ up ht (by omega) hσ h16
      | false =>
        rw [if_neg (by decide), factor_top_empty P n C.hi ℓ (hQt rfl ℓ (Finset.mem_filter.mp hℓ).1),
          r_Dn]
    have hR : ∀ ℓ ∈ Qh, ratProd (restr ℓ (desC P n C.hi C.des)) recip - 1 ≤
        r (clsF first up C - Dn) := by
      intro ℓ hℓ
      have h1 := ratProd_desC_le P hP n hn C.hi C.des hch ℓ (if first then expU (xq up) else Dn) (htop ℓ hℓ) _
        (tail_le_TAILF P hP n hn ℓ)
      have h2 : r (if first then expU (xq up) else Dn) * r (facProd C.des) * r TAILF ≤
          r (clsF first up C) := by
        unfold clsF
        exact mulU_ge_of (mul_nonneg (r_nonneg _) (r_nonneg _)) (r_nonneg _)
          (mulU_ge (if first then expU (xq up) else Dn) (facProd C.des)) le_rfl
      have := r_sub_ge (clsF first up C)
      linarith
    have hcls := class_err_le P hP Qh hQhP (desC P n C.hi C.des) _ _ _ (r_nonneg _)
      (r_nonneg _) hs hW hR
    have hm := mulU_ge_of (x := s + if first then up else 0) (r_nonneg _) (mul_nonneg (r_nonneg _) (r_nonneg _)) le_rfl
      (mulU_ge (expU (xq (up + s))) (clsF first up C - Dn))
    have : r (s + if first then up else 0) * r (expU (xq (up + s))) * r (clsF first up C - Dn) =
        r (s + if first then up else 0) * (r (expU (xq (up + s))) * r (clsF first up C - Dn)) := by
      ring
    linarith

end Shoup.Sieve
