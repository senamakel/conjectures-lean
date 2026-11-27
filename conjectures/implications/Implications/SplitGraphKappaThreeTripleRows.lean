import Implications.SplitGraphTrees

/-! Outside attachments for a four-vertex support with three prescribed triple rows. -/

namespace SplitGraphKappaThreeTripleRows

open SplitGraphTrees

variable {V : Type*} [DecidableEq V]

/-- A row of size at most three which meets the symmetric-difference bound
against three prescribed triples can contain an outside vertex only together
with the common vertex of the triples. -/
theorem outside_row_eq_pair
    (t : Finset V) (a b c d x : V)
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d)
    (hx : x ∈ t) (hout : x ∉ ({a, b, c, d} : Finset V))
    (ht : t.card ≤ 3)
    (hB : (t \ {a, b, c} ∪ {a, b, c} \ t).card ≤ 3)
    (hC : (t \ {a, b, d} ∪ {a, b, d} \ t).card ≤ 3)
    (hD : (t \ {a, c, d} ∪ {a, c, d} \ t).card ≤ 3) :
    t = {a, x} := by
  let Q := t.erase x
  have hQcard : Q.card + 1 = t.card := by
    have he := Finset.card_erase_of_mem hx
    have hp := Finset.card_pos.mpr ⟨x, hx⟩
    change (t.erase x).card + 1 = t.card
    omega
  have htriple (s : Finset V) (hsc : s.card = 3) (hxs : x ∉ s)
      (hdiff : (t \ s ∪ s \ t).card ≤ 3) :
      Q.Nonempty ∧ Q ⊆ s := by
    have hd : Disjoint (t \ s) (s \ t) := by
      apply Finset.disjoint_left.mpr
      intro y hy hz
      exact (Finset.mem_sdiff.mp hy).2 (Finset.mem_sdiff.mp hz).1
    rw [Finset.card_union_of_disjoint hd] at hdiff
    have ht' := Finset.card_sdiff_add_card_inter t s
    have hs' := Finset.card_sdiff_add_card_inter s t
    rw [Finset.inter_comm s t] at hs'
    have hi : t.card ≤ 2 * (t ∩ s).card := by omega
    have hsub : t ∩ s ⊆ Q := by
      intro y hy
      obtain ⟨hyt, hys⟩ := Finset.mem_inter.mp hy
      exact Finset.mem_erase.mpr ⟨fun hyx => hxs (hyx ▸ hys), hyt⟩
    have htQ := Finset.card_le_card hsub
    refine ⟨Finset.card_pos.mp (by omega), ?_⟩
    intro y hyQ
    by_contra hys
    have hsub' : t ∩ s ⊆ Q.erase y := by
      intro z hz
      exact Finset.mem_erase.mpr ⟨fun hzy => hys (hzy ▸ (Finset.mem_inter.mp hz).2), hsub hz⟩
    have hi' := Finset.card_le_card hsub'
    rw [Finset.card_erase_of_mem hyQ] at hi'
    omega
  have hout' : x ≠ a ∧ x ≠ b ∧ x ≠ c ∧ x ≠ d := by
    simpa only [Finset.mem_insert, Finset.mem_singleton, not_or] using hout
  have hB' := htriple {a, b, c} (by simp [hab, hac, hbc]) (by
    simp [hout'.1, hout'.2.1, hout'.2.2.1]) hB
  have hC' := htriple {a, b, d} (by simp [hab, had, hbd]) (by
    simp [hout'.1, hout'.2.1, hout'.2.2.2]) hC
  have hD' := htriple {a, c, d} (by simp [hac, had, hcd]) (by
    simp [hout'.1, hout'.2.2.1, hout'.2.2.2]) hD
  have hQsub : Q ⊆ {a} := by
    intro y hy
    have hBmem := hB'.2 hy
    have hCmem := hC'.2 hy
    have hDmem := hD'.2 hy
    simp only [Finset.mem_insert, Finset.mem_singleton] at hBmem hCmem hDmem ⊢
    rcases hBmem with h | h | h
    · exact h
    · subst y
      simp [hab.symm, hbc, hbd] at hDmem
    · subst y
      simp [hac.symm, hbc.symm, hcd] at hCmem
  obtain ⟨y, hy⟩ := hB'.1
  have hya := Finset.mem_singleton.mp (hQsub hy)
  have hQeq : Q = {a} := Finset.Subset.antisymm hQsub (Finset.singleton_subset_iff.mpr (hya ▸ hy))
  calc
    t = insert x Q := (Finset.insert_erase hx).symm
    _ = {a, x} := by rw [hQeq, Finset.pair_comm]

/-- Row size and row difference alone determine every attachment to an
independent vertex outside the support of the three triples. -/
theorem outside_attachment_row
    (G : SimpleGraph V) (C I : Finset V)
    (a b c d qB qC qD : V)
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d)
    (hqB : qB ∈ C) (hqC : qC ∈ C) (hqD : qD ∈ C)
    (hB : row G I qB = {a, b, c}) (hC : row G I qC = {a, b, d})
    (hD : row G I qD = {a, c, d})
    (hsizes : ∀ q ∈ C, (row G I q).card ≤ 3)
    (hdiffs : ∀ q ∈ C, ∀ r ∈ C, q ≠ r → (rowDiff G I q r).card ≤ 3) :
    ∀ q ∈ C, ∀ x ∈ I \ {a, b, c, d}, G.Adj q x → row G I q = {a, x} := by
  intro q hq x hx hadj
  obtain ⟨hxI, hout⟩ := Finset.mem_sdiff.mp hx
  have hmem : x ∈ row G I q := by simp [row, hxI, hadj]
  have hdiff (r : V) (hr : r ∈ C) (s : Finset V)
      (heq : row G I r = s) (hnot : x ∉ s) :
      ((row G I q) \ s ∪ s \ (row G I q)).card ≤ 3 := by
    have hne : q ≠ r := by
      intro h
      exact hnot (heq ▸ (h ▸ hmem))
    simpa [rowDiff, heq] using hdiffs q hq r hr hne
  have hout' : x ≠ a ∧ x ≠ b ∧ x ≠ c ∧ x ≠ d := by
    simpa only [Finset.mem_insert, Finset.mem_singleton, not_or] using hout
  exact outside_row_eq_pair (row G I q) a b c d x hab hac had hbc hbd hcd hmem hout
    (hsizes q hq)
    (hdiff qB hqB _ hB (by simp [hout'.1, hout'.2.1, hout'.2.2.1]))
    (hdiff qC hqC _ hC (by simp [hout'.1, hout'.2.1, hout'.2.2.2]))
    (hdiff qD hqD _ hD (by simp [hout'.1, hout'.2.2.1, hout'.2.2.2]))

#print axioms outside_row_eq_pair
#print axioms outside_attachment_row

end SplitGraphKappaThreeTripleRows
