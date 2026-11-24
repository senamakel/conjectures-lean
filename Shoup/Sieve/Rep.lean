import Shoup.Sieve.Bonferroni

/-!
# Squarefree monomial expansions

`IsRep F S M` says that `F y = Σ_i c_i ∏_{ℓ ∈ U_i} y ℓ` for a finite list of pairs `(U_i, c_i)`
with every `U_i ⊆ S` and `Σ |c_i| ≤ M`. Such expansions are what the transfer to character sums
needs: each monomial `∏_{ℓ∈U} y ℓ` becomes the count of `∏ U`-th power residues.
-/

namespace Shoup.Sieve

open Finset

/-- A finite linear combination of squarefree monomials. -/
abbrev Terms := List (Finset ℕ × ℝ)

/-- Evaluation of a linear combination of monomials. -/
noncomputable def ev (L : Terms) (y : ℕ → ℝ) : ℝ :=
  (L.map fun q => q.2 * ∏ ℓ ∈ q.1, y ℓ).sum

/-- Sum of the absolute values of the coefficients. -/
noncomputable def mass (L : Terms) : ℝ := (L.map fun q => |q.2|).sum

/-- `F` is a combination of monomials supported in `S`, of mass at most `M`. -/
def IsRep (F : (ℕ → ℝ) → ℝ) (S : Finset ℕ) (M : ℝ) : Prop :=
  ∃ L : Terms, (∀ q ∈ L, q.1 ⊆ S) ∧ mass L ≤ M ∧ ∀ y, F y = ev L y

lemma mass_nonneg (L : Terms) : 0 ≤ mass L := by
  unfold mass
  exact List.sum_nonneg fun x hx => by
    obtain ⟨q, _, rfl⟩ := List.mem_map.mp hx; exact abs_nonneg _

lemma ev_append (L L' : Terms) (y : ℕ → ℝ) : ev (L ++ L') y = ev L y + ev L' y := by
  simp [ev]

lemma mass_append (L L' : Terms) : mass (L ++ L') = mass L + mass L' := by
  simp [mass]

/-- Multiply every coefficient by `c`. -/
def smulT (c : ℝ) (L : Terms) : Terms := L.map fun q => (q.1, c * q.2)

lemma ev_smulT (c : ℝ) (L : Terms) (y : ℕ → ℝ) : ev (smulT c L) y = c * ev L y := by
  induction L with
  | nil => simp [ev, smulT]
  | cons q L ih =>
    simp only [ev, smulT, List.map_cons, List.sum_cons] at ih ⊢
    rw [ih]; ring

lemma mass_smulT (c : ℝ) (L : Terms) : mass (smulT c L) = |c| * mass L := by
  induction L with
  | nil => simp [mass, smulT]
  | cons q L ih =>
    simp only [mass, smulT, List.map_cons, List.sum_cons] at ih ⊢
    rw [ih, abs_mul]; ring

/-- Product of two combinations (supports are merged by union). -/
def mulT (L L' : Terms) : Terms :=
  L.flatMap fun q => L'.map fun q' => (q.1 ∪ q'.1, q.2 * q'.2)

lemma ev_mulT (L L' : Terms) (S S' : Finset ℕ) (hL : ∀ q ∈ L, q.1 ⊆ S)
    (hL' : ∀ q ∈ L', q.1 ⊆ S') (hd : Disjoint S S') (y : ℕ → ℝ) :
    ev (mulT L L') y = ev L y * ev L' y := by
  induction L with
  | nil => simp [ev, mulT]
  | cons q L ih =>
    have ih' := ih (fun q' h => hL q' (List.mem_cons_of_mem _ h))
    simp only [mulT, List.flatMap_cons] at ih' ⊢
    rw [ev_append, ih']
    have hq := hL q List.mem_cons_self
    have : ev (List.map (fun q' => (q.1 ∪ q'.1, q.2 * q'.2)) L') y =
        (q.2 * ∏ ℓ ∈ q.1, y ℓ) * ev L' y := by
      clear ih ih'
      induction L' with
      | nil => simp [ev]
      | cons q' L' ih2 =>
        have ih2' := ih2 (fun r h => hL' r (List.mem_cons_of_mem _ h))
        simp only [ev, List.map_cons, List.sum_cons] at ih2' ⊢
        rw [ih2']
        have hq' := hL' q' List.mem_cons_self
        rw [Finset.prod_union (Finset.disjoint_of_subset_left hq
          (Finset.disjoint_of_subset_right hq' hd))]
        ring
    rw [this]
    simp only [ev, List.map_cons, List.sum_cons]
    ring

lemma mass_mulT (L L' : Terms) : mass (mulT L L') = mass L * mass L' := by
  induction L with
  | nil => simp [mass, mulT]
  | cons q L ih =>
    simp only [mulT, List.flatMap_cons] at ih ⊢
    rw [mass_append, ih]
    have : mass (List.map (fun q' => (q.1 ∪ q'.1, q.2 * q'.2)) L') = |q.2| * mass L' := by
      clear ih
      induction L' with
      | nil => simp [mass]
      | cons q' L' ih2 =>
        simp only [mass, List.map_cons, List.sum_cons] at ih2 ⊢
        rw [ih2, abs_mul]; ring
    rw [this]
    simp only [mass, List.map_cons, List.sum_cons]
    ring

namespace IsRep

lemma mono {F : (ℕ → ℝ) → ℝ} {S S' : Finset ℕ} {M M' : ℝ} (h : IsRep F S M) (hS : S ⊆ S')
    (hM : M ≤ M') : IsRep F S' M' := by
  obtain ⟨L, h1, h2, h3⟩ := h
  exact ⟨L, fun q hq => (h1 q hq).trans hS, h2.trans hM, h3⟩

lemma nonneg {F : (ℕ → ℝ) → ℝ} {S : Finset ℕ} {M : ℝ} (h : IsRep F S M) : 0 ≤ M := by
  obtain ⟨L, _, h2, _⟩ := h
  exact (mass_nonneg L).trans h2

lemma congr {F F' : (ℕ → ℝ) → ℝ} {S : Finset ℕ} {M : ℝ} (h : IsRep F S M)
    (hF : ∀ y, F' y = F y) : IsRep F' S M := by
  obtain ⟨L, h1, h2, h3⟩ := h
  exact ⟨L, h1, h2, fun y => (hF y).trans (h3 y)⟩

lemma one : IsRep (fun _ => 1) ∅ 1 :=
  ⟨[(∅, 1)], by simp, by simp [mass], fun y => by simp [ev]⟩

lemma sub {F G : (ℕ → ℝ) → ℝ} {S : Finset ℕ} {M N : ℝ} (hF : IsRep F S M) (hG : IsRep G S N) :
    IsRep (fun y => F y - G y) S (M + N) := by
  obtain ⟨L, h1, h2, h3⟩ := hF
  obtain ⟨L', h1', h2', h3'⟩ := hG
  refine ⟨L ++ smulT (-1) L', fun q hq => ?_, ?_, fun y => ?_⟩
  · rcases List.mem_append.mp hq with h | h
    · exact h1 q h
    · obtain ⟨q', hq', rfl⟩ := List.mem_map.mp h
      exact h1' q' hq'
  · rw [mass_append, mass_smulT]; simp; linarith
  · dsimp only; rw [ev_append, ev_smulT, h3, h3']; ring

lemma mul {F G : (ℕ → ℝ) → ℝ} {S S' : Finset ℕ} {M N : ℝ} (hF : IsRep F S M)
    (hG : IsRep G S' N) (hd : Disjoint S S') :
    IsRep (fun y => F y * G y) (S ∪ S') (M * N) := by
  obtain ⟨L, h1, h2, h3⟩ := hF
  obtain ⟨L', h1', h2', h3'⟩ := hG
  refine ⟨mulT L L', fun q hq => ?_, ?_, fun y => ?_⟩
  · obtain ⟨r, hr, hq'⟩ := List.mem_flatMap.mp hq
    obtain ⟨r', hr', rfl⟩ := List.mem_map.mp hq'
    exact Finset.union_subset_union (h1 r hr) (h1' r' hr')
  · rw [mass_mulT]
    exact mul_le_mul h2 h2' (mass_nonneg _) ((mass_nonneg _).trans h2)
  · dsimp only; rw [ev_mulT L L' S S' h1 h1' hd, h3, h3']

/-- A sum over a finset of monomials with coefficients. -/
lemma finsetSum (𝒯 : Finset (Finset ℕ)) (c : Finset ℕ → ℝ) (S : Finset ℕ)
    (h𝒯 : ∀ T ∈ 𝒯, T ⊆ S) :
    IsRep (fun y => ∑ T ∈ 𝒯, c T * ∏ ℓ ∈ T, y ℓ) S (∑ T ∈ 𝒯, |c T|) := by
  refine ⟨𝒯.toList.map fun T => (T, c T), fun q hq => ?_, ?_, fun y => ?_⟩
  · obtain ⟨T, hT, rfl⟩ := List.mem_map.mp hq
    exact h𝒯 T (Finset.mem_toList.mp hT)
  · unfold mass; rw [List.map_map]
    exact le_of_eq (Finset.sum_map_toList 𝒯 _)
  · unfold ev; rw [List.map_map]
    exact (Finset.sum_map_toList 𝒯 _).symm

end IsRep

/-- The truncated inclusion–exclusion is a combination of `#{T ⊆ B, |T| < m}` monomials. -/
lemma isRep_G (m : ℕ) (B : Finset ℕ) :
    IsRep (G m B) B ((B.card + 1 : ℝ) ^ m) := by
  have h := IsRep.finsetSum (B.powerset.filter fun T => T.card < m)
    (fun T => (-1 : ℝ) ^ T.card) B (fun T hT => Finset.mem_powerset.mp (Finset.mem_filter.mp hT).1)
  refine (h.congr fun y => ?_).mono le_rfl ?_
  · unfold G; rw [Finset.sum_filter]
  · simp only [abs_pow, abs_neg, abs_one, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one]
    -- `#{T ⊆ B : |T| < m} ≤ Σ_{i<m} C(n,i) ≤ (n+1)^m`
    have hcard : (B.powerset.filter fun T => T.card < m).card ≤ (B.card + 1) ^ m := by
      calc (B.powerset.filter fun T => T.card < m).card
          = ∑ i ∈ Finset.range m, (B.powersetCard i).card := by
            rw [Finset.card_eq_sum_card_fiberwise (f := Finset.card) (t := Finset.range m)
              (fun T hT => Finset.mem_range.mpr (Finset.mem_filter.mp hT).2)]
            refine Finset.sum_congr rfl fun i hi => ?_
            congr 1
            ext T
            simp only [Finset.mem_filter, Finset.mem_powerset, Finset.mem_powersetCard]
            constructor
            · rintro ⟨⟨h1, _⟩, h2⟩; exact ⟨h1, h2⟩
            · rintro ⟨h1, h2⟩; exact ⟨⟨h1, h2 ▸ Finset.mem_range.mp hi⟩, h2⟩
        _ ≤ ∑ i ∈ Finset.range (m + 1), B.card ^ i * 1 ^ (m - i) * m.choose i := by
            rw [Finset.sum_range_succ]
            refine le_add_right (Finset.sum_le_sum fun i hi => ?_)
            rw [Finset.card_powersetCard, one_pow, mul_one]
            have h1 := Nat.choose_le_pow B.card i
            have h2 : 1 ≤ m.choose i := Nat.choose_pos (Finset.mem_range.mp hi).le
            nlinarith
        _ = (B.card + 1) ^ m := (add_pow _ _ _).symm
    exact_mod_cast hcard

lemma isRep_E (m : ℕ) (B : Finset ℕ) :
    IsRep (E m B) B ((B.card + 1 : ℝ) ^ m) := by
  have h := IsRep.finsetSum (B.powersetCard m) (fun _ => 1) B
    (fun T hT => (Finset.mem_powersetCard.mp hT).1)
  refine (h.congr fun y => ?_).mono le_rfl ?_
  · simp [E]
  · simp only [abs_one, Finset.sum_const, nsmul_eq_mul, mul_one, Finset.card_powersetCard]
    have h1 := Nat.choose_le_pow B.card m
    have h2 : B.card ^ m ≤ (B.card + 1) ^ m := Nat.pow_le_pow_left (Nat.le_succ _) m
    exact_mod_cast h1.trans h2

end Shoup.Sieve
