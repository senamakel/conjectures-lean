import Shoup.Sieve.Table

/-!
# The mass of the Buchstab sieve built from a table

`massU (desC P n hi rs) ≤ Cbot · 2^{600} · 2^{n (massE rs + 29)}` (`massU_desC_le`), and the
sum over `ℓ` of the masses of the chosen designs is at most
`(|tab| + 1) · Cbot · 2^{600} · 2^{n (S - 1)}` when every class satisfies
`hi + 30 + massE ≤ S` (`mass_table_le`).
-/

namespace Shoup.Sieve

open Finset Fixed

lemma massU_append (L₁ L₂ : List Block) : massU (L₁ ++ L₂) = massU L₁ * massU L₂ := by
  induction L₁ with
  | nil => simp [massU]
  | cons b L ih => simp only [List.cons_append, massU, ih]; ring

lemma massU_restr_le (ℓ : ℕ) (L : List Block) : massU (restr ℓ L) ≤ massU L := by
  induction L with
  | nil => simp [restr, massU]
  | cons b L ih =>
    show ((b.1.filter (· < ℓ)).card + 1 : ℝ) ^ (2 * b.2) * massU (restr ℓ L) ≤
      ((b.1.card + 1 : ℝ) ^ (2 * b.2)) * massU L
    have hc : ((b.1.filter (· < ℓ)).card : ℝ) ≤ b.1.card := by
      exact_mod_cast Finset.card_filter_le _ _
    have h1 : ((b.1.filter (· < ℓ)).card + 1 : ℝ) ^ (2 * b.2) ≤ ((b.1.card + 1 : ℝ) ^ (2 * b.2)) :=
      pow_le_pow_left₀ (by positivity) (by linarith) _
    exact mul_le_mul h1 ih (massU_nonneg _) (by positivity)

lemma card_le_pow_of_le (P : Finset ℕ) (hP : ∀ ℓ ∈ P, ℓ.Prime) (B : Finset ℕ) (hB : B ⊆ P) (e : ℕ)
    (h : ∀ ℓ ∈ B, ℓ ≤ 2 ^ e) : B.card ≤ 2 ^ e := by
  have hsub : B ⊆ Finset.Icc 1 (2 ^ e) := fun ℓ hℓ =>
    Finset.mem_Icc.mpr ⟨(hP ℓ (hB hℓ)).one_lt.le, h ℓ hℓ⟩
  have := Finset.card_le_card hsub
  rwa [Nat.card_Icc, Nat.add_sub_cancel] at this

lemma block_mass_le (c e k : ℕ) (hc : c ≤ 2 ^ e) :
    ((c : ℝ) + 1) ^ (2 * k) ≤ (2 : ℝ) ^ ((e + 1) * (2 * k)) := by
  have hcR : (c : ℝ) + 1 ≤ 2 ^ (e + 1) := by
    have : (c : ℝ) ≤ 2 ^ e := by exact_mod_cast hc
    have : (1 : ℝ) ≤ 2 ^ e := one_le_pow₀ (by norm_num)
    rw [pow_succ]; linarith
  calc ((c : ℝ) + 1) ^ (2 * k) ≤ ((2 : ℝ) ^ (e + 1)) ^ (2 * k) :=
        pow_le_pow_left₀ (by positivity) hcR _
    _ = _ := (pow_mul _ _ _).symm

lemma massU_cust_le (P : Finset ℕ) (hP : ∀ ℓ ∈ P, ℓ.Prime) (n : ℕ) :
    ∀ (rs : List Row), massU (custBlocks P n rs) ≤ (2 : ℝ) ^ (n * massE rs + kSum rs) := by
  intro rs
  induction rs with
  | nil => simp [custBlocks, massU, massE, kSum]
  | cons x rs ih =>
    rcases x with ⟨a, b, k, c⟩
    show ((P.filter fun ℓ => 2 ^ (b * n) < ℓ ∧ ℓ ≤ 2 ^ (a * n)).card + 1 : ℝ) ^ (2 * k) *
        massU (custBlocks P n rs) ≤ (2 : ℝ) ^ (n * (2 * k * a + massE rs) + (2 * k + kSum rs))
    have hc := card_le_pow_of_le P hP (P.filter fun ℓ => 2 ^ (b * n) < ℓ ∧ ℓ ≤ 2 ^ (a * n))
      (Finset.filter_subset _ _) (a * n) (fun ℓ h => (Finset.mem_filter.mp h).2.2)
    have h1 := block_mass_le _ _ k hc
    have e : n * (2 * k * a + massE rs) + (2 * k + kSum rs) =
        (a * n + 1) * (2 * k) + (n * massE rs + kSum rs) := by ring
    rw [e, pow_add]
    exact mul_le_mul h1 ih (massU_nonneg _) (by positivity)

lemma tail_weight_sum6 (T : ℕ) :
    ∑ i ∈ range T, (2 * (i : ℝ) + 12) / 2 ^ i = 28 - (4 * T + 28) / 2 ^ T := by
  induction T with
  | zero => norm_num
  | succ T ih =>
    rw [Finset.sum_range_succ, ih]
    push_cast
    field_simp
    ring

lemma tail_count_sum6 (T : ℕ) : ∑ i ∈ range T, (2 * (i : ℝ) + 12) ≤ 12 * 2 ^ T := by
  induction T with
  | zero => norm_num
  | succ T ih =>
    rw [Finset.sum_range_succ, pow_succ]
    have : (T : ℝ) + 1 ≤ 2 ^ T := by
      have := Nat.lt_two_pow_self (n := T)
      have : ((T + 1 : ℕ) : ℝ) ≤ ((2 ^ T : ℕ) : ℝ) := by exact_mod_cast this
      push_cast at this; linarith
    linarith

lemma massU_tail_le (P : Finset ℕ) (hP : ∀ ℓ ∈ P, ℓ.Prime) (n : ℕ) (hn : 2 ^ 23 ≤ n) :
    massU (tailPart P n) ≤ Cbot * 2 ^ (29 * n) := by
  obtain ⟨hT1, hT2⟩ := Tn1_facts n hn
  unfold tailPart
  simp only [massU]
  rw [massU_map_range]
  have hbot : ((botT P (tailE n) (Tn1 n) kbot).1.card + 1 : ℝ) ^
      (2 * (botT P (tailE n) (Tn1 n) kbot).2) ≤ Cbot := by
    have hK : tailE n (Tn1 n) ≤ 2 * Ubot := by
      unfold tailE
      exact ((Nat.div_lt_iff_lt_mul (by positivity)).mpr (by linarith)).le
    have hc : (botT P (tailE n) (Tn1 n) kbot).1.card ≤ 2 ^ (2 * Ubot) :=
      (card_filter_le_pow P hP _ _ fun ℓ h => h).trans (Nat.pow_le_pow_right (by norm_num) hK)
    have hcR : ((botT P (tailE n) (Tn1 n) kbot).1.card : ℝ) ≤ 2 ^ (2 * Ubot) := by
      exact_mod_cast hc
    unfold Cbot
    simp only [botT] at hcR ⊢
    gcongr
  have hmid : ∏ i ∈ range (Tn1 n), ((midT P (tailE n) tailLev i).1.card + 1 : ℝ) ^
      (2 * (midT P (tailE n) tailLev i).2) ≤ 2 ^ (29 * n) := by
    calc ∏ i ∈ range (Tn1 n), ((midT P (tailE n) tailLev i).1.card + 1 : ℝ) ^
          (2 * (midT P (tailE n) tailLev i).2)
        ≤ ∏ i ∈ range (Tn1 n), (2 : ℝ) ^ ((tailE n i + 1) * (2 * tailLev i)) := by
          refine Finset.prod_le_prod₀ (fun i _ => by positivity) fun i _ => ?_
          exact block_mass_le _ _ _ (card_filter_le_pow P hP _ _ fun ℓ h => h.2)
      _ = (2 : ℝ) ^ (∑ i ∈ range (Tn1 n), (tailE n i + 1) * (2 * tailLev i)) :=
          Finset.prod_pow_eq_pow_sum _ _ _
      _ ≤ 2 ^ (29 * n) := by
          apply pow_le_pow_right₀ (by norm_num)
          have hR : ((∑ i ∈ range (Tn1 n), (tailE n i + 1) * (2 * tailLev i) : ℕ) : ℝ) ≤
              29 * n := by
            push_cast
            have hterm : ∀ i ∈ range (Tn1 n), (((tailE n i : ℕ) : ℝ) + 1) * (2 * ((i + 6 : ℕ) : ℝ)) ≤
                n * ((2 * (i : ℝ) + 12) / 2 ^ i) + (2 * (i : ℝ) + 12) := by
              intro i _
              have : ((tailE n i : ℕ) : ℝ) ≤ (n : ℝ) / 2 ^ i := by
                have := Nat.cast_div_le (α := ℝ) (m := n) (n := 2 ^ i)
                push_cast at this; exact this
              push_cast
              have h6 : (0 : ℝ) ≤ 2 * ((i : ℝ) + 6) := by positivity
              calc (((tailE n i : ℕ) : ℝ) + 1) * (2 * ((i : ℝ) + 6))
                  ≤ ((n : ℝ) / 2 ^ i + 1) * (2 * ((i : ℝ) + 6)) := by gcongr
                _ = _ := by ring
            simp only [tailLev]
            refine (Finset.sum_le_sum hterm).trans ?_
            rw [Finset.sum_add_distrib, ← Finset.mul_sum, tail_weight_sum6]
            have h1 := tail_count_sum6 (Tn1 n)
            have h2 : (0 : ℝ) ≤ (4 * (Tn1 n : ℝ) + 28) / 2 ^ Tn1 n := by positivity
            have h3 : 12 * (2 : ℝ) ^ Tn1 n ≤ n := by
              rw [Ubot_def] at hT1
              have : ((2 ^ 20 * 2 ^ Tn1 n : ℕ) : ℝ) ≤ ((n : ℕ) : ℝ) := by exact_mod_cast hT1
              push_cast at this
              have : (0 : ℝ) ≤ 2 ^ Tn1 n := by positivity
              linarith
            have hn0 : (0 : ℝ) ≤ n := by positivity
            nlinarith
          exact_mod_cast hR
  have hC0 : 0 ≤ Cbot := by unfold Cbot; positivity
  have h0 : (0 : ℝ) ≤ ∏ i ∈ range (Tn1 n), ((midT P (tailE n) tailLev i).1.card + 1 : ℝ) ^
      (2 * (midT P (tailE n) tailLev i).2) := Finset.prod_nonneg fun i _ => by positivity
  exact mul_le_mul hbot hmid h0 hC0

lemma massU_desC_le (P : Finset ℕ) (hP : ∀ ℓ ∈ P, ℓ.Prime) (n : ℕ) (hn : 2 ^ 23 ≤ n) (hi : ℕ)
    (rs : List Row) (hk : kSum rs ≤ 600) :
    massU (desC P n hi rs) ≤ Cbot * 2 ^ 600 * 2 ^ (n * (massE rs + 29)) := by
  have e : massU (desC P n hi rs) =
      ((((P.filter fun ℓ => 2 ^ (hi * n) < ℓ)).card + 1 : ℝ) ^ (2 * 0)) *
        massU (custBlocks P n rs ++ tailPart P n) := rfl
  rw [e, mul_zero, pow_zero, one_mul, massU_append]
  have h1 := massU_cust_le P hP n rs
  have h2 := massU_tail_le P hP n hn
  have hC0 : 0 ≤ Cbot := by unfold Cbot; positivity
  have h3 : (2 : ℝ) ^ (n * massE rs + kSum rs) ≤ 2 ^ 600 * 2 ^ (n * massE rs) := by
    rw [pow_add, mul_comm]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hk) (by positivity)
  calc massU (custBlocks P n rs) * massU (tailPart P n)
      ≤ (2 ^ 600 * 2 ^ (n * massE rs)) * (Cbot * 2 ^ (29 * n)) :=
        mul_le_mul (h1.trans h3) h2 (massU_nonneg _) (by positivity)
    _ = Cbot * 2 ^ 600 * 2 ^ (n * (massE rs + 29)) := by
        rw [show n * (massE rs + 29) = n * massE rs + 29 * n by ring, pow_add]; ring

/-- The constant `Cbot · 2^{600}`. -/
noncomputable def Kmass : ℝ := Cbot * 2 ^ 600

lemma Kmass_nonneg : 0 ≤ Kmass := by unfold Kmass Cbot; positivity

theorem mass_table_le (P : Finset ℕ) (hP : ∀ ℓ ∈ P, ℓ.Prime) (n : ℕ) (hn : 2 ^ 36 ≤ n) (S : ℕ)
    (hS : 31 ≤ S) :
    ∀ (tab : List Cls) (first : Bool) (up t : ℕ) (Q : Finset ℕ),
      tableOK S first up t tab = true → Q ⊆ P →
      Q.card ≤ 2 ^ (t * n) → (first = false → ∀ ℓ ∈ Q, ℓ ≤ 2 ^ (t * n)) →
      ∑ ℓ ∈ Q, massU (restr ℓ (pick (desC P n 1 []) ℓ (custList P n tab))) ≤
        (tab.length + 1 : ℝ) * Kmass * 2 ^ (n * (S - 1)) := by
  have hn23 : 2 ^ 23 ≤ n := by omega
  have hdesC : ∀ (hi : ℕ) (rs : List Row) (Q : Finset ℕ), kSum rs ≤ 600 →
      hi + 30 + massE rs ≤ S → Q.card ≤ 2 ^ (hi * n) →
      ∑ ℓ ∈ Q, massU (restr ℓ (desC P n hi rs)) ≤ Kmass * 2 ^ (n * (S - 1)) := by
    intro hi rs Q hk hm hc
    have h1 : ∀ ℓ ∈ Q, massU (restr ℓ (desC P n hi rs)) ≤ Kmass * 2 ^ (n * (massE rs + 29)) :=
      fun ℓ _ => (massU_restr_le ℓ _).trans (massU_desC_le P hP n hn23 hi rs hk)
    refine (Finset.sum_le_sum h1).trans ?_
    rw [Finset.sum_const, nsmul_eq_mul]
    have hcR : (Q.card : ℝ) ≤ 2 ^ (hi * n) := by exact_mod_cast hc
    have hK := Kmass_nonneg
    calc (Q.card : ℝ) * (Kmass * 2 ^ (n * (massE rs + 29)))
        ≤ 2 ^ (hi * n) * (Kmass * 2 ^ (n * (massE rs + 29))) :=
          mul_le_mul_of_nonneg_right hcR (by positivity)
      _ = Kmass * 2 ^ (n * (hi + massE rs + 29)) := by
          rw [show n * (hi + massE rs + 29) = hi * n + n * (massE rs + 29) by ring, pow_add]; ring
      _ ≤ Kmass * 2 ^ (n * (S - 1)) := by
          apply mul_le_mul_of_nonneg_left _ hK
          exact pow_le_pow_right₀ (by norm_num) (Nat.mul_le_mul_left n (by omega))
  intro tab
  induction tab with
  | nil =>
    intro first up t Q hok hQ hc hQt
    simp only [tableOK, Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq, decide_eq_true_eq] at hok
    obtain ⟨⟨⟨hf, ht1⟩, _⟩, _⟩ := hok
    subst ht1
    simp only [pick, custList, List.length_nil, Nat.cast_zero, zero_add, one_mul]
    exact hdesC 1 [] Q (by simp [kSum]) (by simp [massE]; omega) hc
  | cons C rest ih =>
    intro first up t Q hok hQ hc hQt
    simp only [tableOK, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hok
    obtain ⟨⟨⟨⟨⟨⟨⟨hhi, hrow⟩, _⟩, _⟩, _⟩, hm⟩, hk⟩, hrest⟩ := hok
    subst hhi
    have hrow' := hrow
    simp only [rowOK, Bool.and_eq_true, decide_eq_true_eq] at hrow'
    obtain ⟨⟨⟨⟨hlo0, hlohi⟩, _⟩, _⟩, _⟩ := hrow'
    rw [← Finset.sum_filter_add_sum_filter_not Q (fun ℓ => 2 ^ (C.lo * n) < ℓ)]
    have hhiQ : ∑ ℓ ∈ Q.filter (fun ℓ => 2 ^ (C.lo * n) < ℓ),
        massU (restr ℓ (pick (desC P n 1 []) ℓ (custList P n (C :: rest)))) =
        ∑ ℓ ∈ Q.filter (fun ℓ => 2 ^ (C.lo * n) < ℓ), massU (restr ℓ (desC P n C.hi C.des)) := by
      refine Finset.sum_congr rfl fun ℓ hℓ => ?_
      simp only [custList, pick, if_pos (Finset.mem_filter.mp hℓ).2]
    have hloQ : ∑ ℓ ∈ Q.filter (fun ℓ => ¬ 2 ^ (C.lo * n) < ℓ),
        massU (restr ℓ (pick (desC P n 1 []) ℓ (custList P n (C :: rest)))) =
        ∑ ℓ ∈ Q.filter (fun ℓ => ¬ 2 ^ (C.lo * n) < ℓ),
          massU (restr ℓ (pick (desC P n 1 []) ℓ (custList P n rest))) := by
      refine Finset.sum_congr rfl fun ℓ hℓ => ?_
      simp only [custList, pick, if_neg (Finset.mem_filter.mp hℓ).2]
    rw [hhiQ, hloQ]
    have h1 := hdesC C.hi C.des (Q.filter fun ℓ => 2 ^ (C.lo * n) < ℓ) hk hm
      ((Finset.card_filter_le _ _).trans hc)
    have hQlo : Q.filter (fun ℓ => ¬ 2 ^ (C.lo * n) < ℓ) ⊆ P := (Finset.filter_subset _ _).trans hQ
    have h2 := ih false (up + sigq C.hi C.lo C.cl) C.lo _ hrest hQlo
      (card_le_pow_of_le P hP _ hQlo _ fun ℓ h => by
        have := (Finset.mem_filter.mp h).2; omega)
      (fun _ ℓ h => by have := (Finset.mem_filter.mp h).2; omega)
    simp only [List.length_cons] at h2 ⊢
    push_cast at h2 ⊢
    linarith

end Shoup.Sieve
