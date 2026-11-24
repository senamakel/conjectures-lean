import Shoup.Sieve.Factor

/-!
# Block designs from a table

A table row `(a, b, k, c)` is the block `{ℓ ∈ P : 2^{bn} < ℓ ≤ 2^{an}}` at level `k`, with
`c / D ≥ log(a/b)`. A chain of rows from `hi` down to `1` (`chainOK`) covers `(2^n, 2^{hi n}]`.
The design `desC P n hi rows` is

* a level-0 block `{ℓ ∈ P : ℓ > 2^{hi n}}`,
* the rows,
* the tail `tailPart P n`: halving blocks `(2^{n/2^{h+1}}, 2^{n/2^h}]` at level `h + 6` and an
  exact bottom block `ℓ ≤ 2^{n/2^T}`.

It partitions `P` (`desC_supp`, `desC_disj`).
-/

namespace Shoup.Sieve

open Finset Fixed

/-- `(a, b, k, c)`. -/
abbrev Row := ℕ × ℕ × ℕ × ℕ

def custBlocks (P : Finset ℕ) (n : ℕ) : List Row → List Block
  | [] => []
  | x :: rs => (P.filter (fun ℓ => 2 ^ (x.2.1 * n) < ℓ ∧ ℓ ≤ 2 ^ (x.1 * n)), x.2.2.1) ::
      custBlocks P n rs

/-- The rows descend from `t` to `1`, each row admissible. -/
def chainOK : ℕ → List Row → Bool
  | t, [] => t == 1
  | t, x :: rs => x.1 == t && rowOK x.1 x.2.1 x.2.2.1 x.2.2.2 && chainOK x.2.1 rs

def tailE (n j : ℕ) : ℕ := n / 2 ^ j

def tailLev (j : ℕ) : ℕ := j + 6

/-- Number of halving blocks. -/
def Tn1 (n : ℕ) : ℕ := Nat.log 2 (n / Ubot)

def tailPart (P : Finset ℕ) (n : ℕ) : List Block :=
  botT P (tailE n) (Tn1 n) kbot :: (List.range (Tn1 n)).map (midT P (tailE n) tailLev)

/-- The design for primes up to `2^{hi n}`. -/
def desC (P : Finset ℕ) (n hi : ℕ) (rs : List Row) : List Block :=
  (P.filter (fun ℓ => 2 ^ (hi * n) < ℓ), 0) :: (custBlocks P n rs ++ tailPart P n)

/-! ### Partition -/

lemma supp_append (L₁ L₂ : List Block) : supp (L₁ ++ L₂) = supp L₁ ∪ supp L₂ := by
  induction L₁ with
  | nil => simp [supp]
  | cons b L ih => simp only [List.cons_append, supp, ih, Finset.union_assoc]

lemma disj_append {L₁ L₂ : List Block} (h₁ : Disj L₁) (h₂ : Disj L₂)
    (h : Disjoint (supp L₁) (supp L₂)) : Disj (L₁ ++ L₂) := by
  induction L₁ with
  | nil => simpa using h₂
  | cons b L ih =>
    obtain ⟨hb, hL⟩ := h₁
    have hsub : supp L ⊆ supp (b :: L) := Finset.subset_union_right
    have hbsub : b.1 ⊆ supp (b :: L) := Finset.subset_union_left
    refine ⟨?_, ih hL (Finset.disjoint_of_subset_left hsub h)⟩
    show Disjoint b.1 (supp (L ++ L₂))
    rw [supp_append]
    exact Finset.disjoint_union_right.mpr ⟨hb, Finset.disjoint_of_subset_left hbsub h⟩

lemma tailE_anti (n : ℕ) : ∀ i < Tn1 n, tailE n (i + 1) ≤ tailE n i := by
  intro i _
  unfold tailE
  rw [pow_succ, ← Nat.div_div_eq_div_mul]
  exact Nat.div_le_self _ _

lemma tailPart_spec (P : Finset ℕ) (n : ℕ) :
    Disj (tailPart P n) ∧ ∀ ℓ, ℓ ∈ supp (tailPart P n) ↔ ℓ ∈ P ∧ ℓ ≤ 2 ^ n := by
  have hd := blocksT_disj P tailLev kbot (tailE_anti n)
  have hs := blocksT_supp (e := tailE n) (K := Tn1 n) P tailLev kbot
  have e0 : tailE n 0 = n := by simp [tailE]
  refine ⟨hd.2, fun ℓ => ?_⟩
  have hsupp : supp (blocksT P (tailE n) tailLev (Tn1 n) kbot) =
      (topT P (tailE n)).1 ∪ supp (tailPart P n) := rfl
  rw [hsupp] at hs
  have hd1 : Disjoint (topT P (tailE n)).1 (supp (tailPart P n)) := hd.1
  constructor
  · intro h
    have hP : ℓ ∈ P := by rw [← hs]; exact Finset.mem_union_right _ h
    refine ⟨hP, ?_⟩
    by_contra hc
    push Not at hc
    have : ℓ ∈ (topT P (tailE n)).1 := by
      simp only [topT, Finset.mem_filter, e0]; exact ⟨hP, hc⟩
    exact Finset.disjoint_left.mp hd1 this h
  · rintro ⟨hP, hle⟩
    rw [← hs] at hP
    rcases Finset.mem_union.mp hP with h | h
    · simp only [topT, Finset.mem_filter, e0] at h; omega
    · exact h

lemma cust_spec (P : Finset ℕ) (n : ℕ) : ∀ (rs : List Row) (t : ℕ), chainOK t rs = true →
    Disj (custBlocks P n rs) ∧
      ∀ ℓ, ℓ ∈ supp (custBlocks P n rs) ↔ ℓ ∈ P ∧ 2 ^ n < ℓ ∧ ℓ ≤ 2 ^ (t * n) := by
  intro rs
  induction rs with
  | nil =>
    intro t ht
    simp only [chainOK, beq_iff_eq] at ht
    subst ht
    refine ⟨trivial, fun ℓ => ?_⟩
    simp only [custBlocks, supp, Finset.notMem_empty, false_iff, one_mul]
    omega
  | cons x rs ih =>
    intro t ht
    rcases x with ⟨a, b, k, c⟩
    simp only [chainOK, Bool.and_eq_true, beq_iff_eq] at ht
    obtain ⟨⟨hat, hrow⟩, hch⟩ := ht
    obtain ⟨hd, hs⟩ := ih b hch
    simp only [rowOK, Bool.and_eq_true, decide_eq_true_eq] at hrow
    obtain ⟨⟨⟨⟨hb, hab⟩, _⟩, _⟩, _⟩ := hrow
    have h1 : 2 ^ n ≤ 2 ^ (b * n) := Nat.pow_le_pow_right (by norm_num) (by nlinarith)
    have h2 : 2 ^ (b * n) ≤ 2 ^ (a * n) :=
      Nat.pow_le_pow_right (by norm_num) (Nat.mul_le_mul_right n hab.le)
    subst hat
    refine ⟨⟨Finset.disjoint_left.mpr fun ℓ h h' => ?_, hd⟩, fun ℓ => ?_⟩
    · simp only [Finset.mem_filter] at h
      have := ((hs ℓ).mp h').2.2
      omega
    · show ℓ ∈ (P.filter fun ℓ => 2 ^ (b * n) < ℓ ∧ ℓ ≤ 2 ^ (a * n)) ∪ supp (custBlocks P n rs) ↔ _
      rw [Finset.mem_union, hs, Finset.mem_filter]
      constructor
      · rintro (⟨hP, h3, h4⟩ | ⟨hP, h3, h4⟩)
        · exact ⟨hP, by omega, h4⟩
        · exact ⟨hP, h3, by omega⟩
      · rintro ⟨hP, h3, h4⟩
        by_cases h5 : 2 ^ (b * n) < ℓ
        · exact Or.inl ⟨hP, h5, h4⟩
        · exact Or.inr ⟨hP, h3, by omega⟩

theorem desC_spec (P : Finset ℕ) (n hi : ℕ) (rs : List Row) (hch : chainOK hi rs = true)
    (hhi : 1 ≤ hi) : Disj (desC P n hi rs) ∧ supp (desC P n hi rs) = P := by
  obtain ⟨hdc, hsc⟩ := cust_spec P n rs hi hch
  obtain ⟨hdt, hst⟩ := tailPart_spec P n
  have h1 : 2 ^ n ≤ 2 ^ (hi * n) := Nat.pow_le_pow_right (by norm_num) (by nlinarith)
  have hdisj : Disjoint (supp (custBlocks P n rs)) (supp (tailPart P n)) :=
    Finset.disjoint_left.mpr fun ℓ h h' => by
      have := ((hsc ℓ).mp h).2.1; have := ((hst ℓ).mp h').2; omega
  have hct := disj_append hdc hdt hdisj
  have hsupp : ∀ ℓ, ℓ ∈ supp (custBlocks P n rs ++ tailPart P n) ↔ ℓ ∈ P ∧ ℓ ≤ 2 ^ (hi * n) := by
    intro ℓ
    rw [supp_append, Finset.mem_union, hsc, hst]
    constructor
    · rintro (⟨hP, _, h⟩ | ⟨hP, h⟩)
      · exact ⟨hP, h⟩
      · exact ⟨hP, by omega⟩
    · rintro ⟨hP, h⟩
      by_cases h' : 2 ^ n < ℓ
      · exact Or.inl ⟨hP, h', h⟩
      · exact Or.inr ⟨hP, by omega⟩
  refine ⟨⟨Finset.disjoint_left.mpr fun ℓ h h' => ?_, hct⟩, ?_⟩
  · simp only [Finset.mem_filter] at h
    have := ((hsupp ℓ).mp h').2; omega
  · ext ℓ
    show ℓ ∈ (P.filter fun ℓ => 2 ^ (hi * n) < ℓ) ∪ supp (custBlocks P n rs ++ tailPart P n) ↔ _
    rw [Finset.mem_union, hsupp, Finset.mem_filter]
    constructor
    · rintro (⟨hP, _⟩ | ⟨hP, _⟩) <;> exact hP
    · intro hP
      by_cases h : 2 ^ (hi * n) < ℓ
      · exact Or.inl ⟨hP, h⟩
      · exact Or.inr ⟨hP, by omega⟩

/-! ### Choosing the design by the size of `ℓ` -/

/-- The first entry `(lo, d)` with `ℓ > 2^lo`, else `dflt`. -/
def pick (dflt : List Block) (ℓ : ℕ) : List (ℕ × List Block) → List Block
  | [] => dflt
  | x :: L => if 2 ^ x.1 < ℓ then x.2 else pick dflt ℓ L

lemma pick_mem (dflt : List Block) (ℓ : ℕ) (L : List (ℕ × List Block)) :
    pick dflt ℓ L = dflt ∨ ∃ x ∈ L, pick dflt ℓ L = x.2 := by
  induction L with
  | nil => exact Or.inl rfl
  | cons x L ih =>
    simp only [pick]
    split_ifs
    · exact Or.inr ⟨x, List.mem_cons_self, rfl⟩
    · rcases ih with h | ⟨y, hy, h⟩
      · exact Or.inl h
      · exact Or.inr ⟨y, List.mem_cons_of_mem _ hy, h⟩

theorem admissible_pick (P : Finset ℕ) (dflt : List Block) (L : List (ℕ × List Block))
    (hdf : Disj dflt ∧ supp dflt = P) (hL : ∀ x ∈ L, Disj x.2 ∧ supp x.2 = P) :
    Admissible P (fun ℓ => restr ℓ (pick dflt ℓ L)) := by
  intro ℓ _
  have h : Disj (pick dflt ℓ L) ∧ supp (pick dflt ℓ L) = P := by
    rcases pick_mem dflt ℓ L with h | ⟨x, hx, h⟩ <;> rw [h]
    · exact hdf
    · exact hL x hx
  exact ⟨disj_restr ℓ h.1, by rw [supp_restr, h.2]⟩

end Shoup.Sieve
