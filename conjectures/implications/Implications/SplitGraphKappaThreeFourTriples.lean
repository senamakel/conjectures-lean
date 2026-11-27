import Implications.SplitGraphTrees
import Implications.SplitGraphSmallRowsThree

/-! A clique-ended Hamilton path for the four full triple rows. -/

namespace SplitGraphKappaThreeFourTriples

open SplitGraphTrees

variable {V : Type*} [Fintype V] [DecidableEq V]

private theorem card_le_twice_intersection_of_diff
    (s t : Finset V) (ht : t.card = 3)
    (hdiff : (s \ t ∪ t \ s).card ≤ 3) :
    s.card ≤ 2 * (s ∩ t).card := by
  classical
  have hdisj : Disjoint (s \ t) (t \ s) := by
    rw [Finset.disjoint_left]
    intro x hxS hxT
    exact (Finset.mem_sdiff.mp hxS).2 (Finset.mem_sdiff.mp hxT).1
  have hunion : (s \ t ∪ t \ s).card = (s \ t).card + (t \ s).card :=
    Finset.card_union_of_disjoint hdisj
  have hs : s.card = (s \ t).card + (s ∩ t).card := by
    have h := Finset.card_sdiff_add_card_inter s t
    omega
  have ht' : t.card = (s ∩ t).card + (t \ s).card := by
    have h := Finset.card_sdiff_add_card_inter t s
    rw [Finset.inter_comm] at h
    omega
  have hsum : s.card + t.card = (s \ t ∪ t \ s).card + 2 * (s ∩ t).card := by
    rw [hs, ht', hunion]
    omega
  omega

/-- Four distinct independent vertices whose four triple rows are present
form a clique-ended core. The row bounds and minimum attachment degree force
there to be no other independent vertices, so the four-row prefix extends by
appending the unused clique vertices. -/
theorem hamiltonian_of_all_four_triple_rows
    (G : SimpleGraph V) [DecidableRel G.Adj] (C I : Finset V)
    (a b c d : V) (r : V → V)
    (hC : G.IsClique (C : Set V)) (hCI : Disjoint C I)
    (hpartition : (Finset.univ : Finset V) = C ∪ I)
    (ha : a ∈ I) (hb : b ∈ I) (hc : c ∈ I) (hd : d ∈ I)
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d)
    (hrows : ∀ i ∈ ({a, b, c, d} : Finset V),
      r i ∈ C ∧ row G I (r i) = ({a, b, c, d} : Finset V).erase i)
    (hrow : ∀ q ∈ C, (row G I q).card ≤ 3)
    (hdiff : ∀ q ∈ C, ∀ e ∈ C, q ≠ e → (rowDiff G I q e).card ≤ 3)
    (hdegree : ∀ i ∈ I, 3 ≤ (C.filter fun q => G.Adj q i).card) :
    ∃ u v : V, ∃ p : G.Walk u v, p.IsHamiltonian := by
  classical
  let A : Finset V := {a, b, c, d}
  have hAcard : A.card = 4 := by
    simp [A, hab, hac, had, hbc, hbd, hcd]
  have hAin : A ⊆ I := by
    intro x hx
    simp only [A, Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · exact ha
    · exact hb
    · exact hc
    · exact hd
  have hAeraseCard (i : V) (hi : i ∈ A) : (A.erase i).card = 3 := by
    rw [Finset.card_erase_of_mem hi, hAcard]
  have hrowCard (i : V) (hi : i ∈ A) : (row G I (r i)).card = 3 := by
    rw [(hrows i hi).2]
    exact hAeraseCard i hi

  have hnoOutsideNeighbor (x : V) (hxI : x ∈ I \ A) (q : V) (hq : q ∈ C) :
      ¬ G.Adj q x := by
    intro hqx
    let S := row G I q
    let B := S ∩ A
    have hxS : x ∈ S := by
      simp [S, row, (Finset.mem_sdiff.mp hxI).1, hqx]
    have hxA : x ∉ A := (Finset.mem_sdiff.mp hxI).2
    have hSbound : S.card ≤ 3 := by
      simpa [S] using hrow q hq
    have houtside : 0 < (S \ A).card :=
      Finset.card_pos.mpr ⟨x, Finset.mem_sdiff.mpr ⟨hxS, hxA⟩⟩
    have hdecomp : S.card = (S \ A).card + B.card := by
      have h := Finset.card_sdiff_add_card_inter S A
      dsimp [B]
      omega
    have hBbound : B.card ≤ 2 := by omega
    have hBsub : B ⊆ S := Finset.inter_subset_left

    by_cases hBne : B.Nonempty
    · obtain ⟨i, hiB⟩ := hBne
      have hiA : i ∈ A := (Finset.mem_inter.mp hiB).2
      have hri := hrows i hiA
      have hriC : r i ∈ C := hri.1
      have hqne : q ≠ r i := by
        intro heq
        have hxi : x ∈ row G I (r i) := by
          change x ∈ row G I q at hxS
          rw [heq] at hxS
          exact hxS
        rw [hri.2] at hxi
        exact hxA ((Finset.mem_erase.mp hxi).2)
      have hrowDiff := hdiff q hq (r i) hriC hqne
      have hdiff' : (S \ (A.erase i) ∪ (A.erase i) \ S).card ≤ 3 := by
        simpa [S, A, rowDiff, hri.2] using hrowDiff
      have hinter := card_le_twice_intersection_of_diff S (A.erase i)
        (hAeraseCard i hiA) hdiff'
      have hsubset : S ∩ (A.erase i) ⊆ B.erase i := by
        intro y hy
        have hyS : y ∈ S := (Finset.mem_inter.mp hy).1
        have hyErase : y ∈ A.erase i := (Finset.mem_inter.mp hy).2
        have hyA : y ∈ A := (Finset.mem_erase.mp hyErase).2
        have hyB : y ∈ B := Finset.mem_inter.mpr ⟨hyS, hyA⟩
        exact Finset.mem_erase.mpr ⟨(Finset.mem_erase.mp hyErase).1, hyB⟩
      have hinterBound : (S ∩ (A.erase i)).card ≤ B.card - 1 := by
        calc
          _ ≤ (B.erase i).card := Finset.card_le_card hsubset
          _ = B.card - 1 := Finset.card_erase_of_mem hiB
      have : S.card > 2 * (S ∩ (A.erase i)).card := by omega
      omega
    · have hBempty : B = ∅ := Finset.not_nonempty_iff_eq_empty.mp hBne
      have hia : a ∈ A := by simp [A]
      have hra := hrows a hia
      have hiaT : (S ∩ (A.erase a)).card = 0 := by
        have hsubset : S ∩ (A.erase a) ⊆ B := by
          intro y hy
          exact Finset.mem_inter.mpr
            ⟨(Finset.mem_inter.mp hy).1,
              (Finset.mem_erase.mp (Finset.mem_inter.mp hy).2).2⟩
        have hempty : S ∩ (A.erase a) = ∅ := by
          ext y
          simp only [Finset.mem_inter, Finset.mem_erase, Finset.notMem_empty]
          constructor
          · rintro ⟨hyS, hyNe, hyA⟩
            have hyB : y ∈ B := Finset.mem_inter.mpr ⟨hyS, hyA⟩
            rw [hBempty] at hyB
            simpa [hBempty] using hyB
          · intro hy
            exact False.elim hy
        simp [hempty]
      have hdiffA : (S \ (A.erase a) ∪ (A.erase a) \ S).card ≤ 3 := by
        have hqa : q ≠ r a := by
          intro heq
          have hxa : x ∈ row G I (r a) := by
            change x ∈ row G I q at hxS
            rw [heq] at hxS
            exact hxS
          rw [hra.2] at hxa
          exact hxA ((Finset.mem_erase.mp hxa).2)
        have hd := hdiff q hq (r a) hra.1 hqa
        simpa [S, A, rowDiff, hra.2] using hd
      have hinter := card_le_twice_intersection_of_diff S (A.erase a)
        (hAeraseCard a hia) hdiffA
      rw [hiaT] at hinter
      have hSpos : 0 < S.card := Finset.card_pos.mpr ⟨x, hxS⟩
      omega

  have hnoOutside : I ⊆ A := by
    intro x hx
    by_contra hxA
    have hxDiff : x ∈ I \ A := Finset.mem_sdiff.mpr ⟨hx, hxA⟩
    have hdegreeX := hdegree x hx
    have hempty : C.filter (fun q => G.Adj q x) = ∅ := by
      ext q
      simp only [Finset.mem_filter, Finset.notMem_empty]
      constructor
      · intro hq
        exact hnoOutsideNeighbor x hxDiff q hq.1 hq.2
      · intro hq
        exact False.elim hq
    rw [hempty] at hdegreeX
    simp at hdegreeX

  have hIeq : I = A := Finset.Subset.antisymm hnoOutside hAin
  have hrowInj (i j : V) (hi : i ∈ A) (hj : j ∈ A)
      (heq : r i = r j) : i = j := by
    by_contra hne
    have hsets : A.erase i = A.erase j := by
      calc
        A.erase i = row G I (r i) := (hrows i hi).2.symm
        _ = row G I (r j) := by rw [heq]
        _ = A.erase j := (hrows j hj).2
    have hmem : i ∈ A.erase j := Finset.mem_erase.mpr ⟨hne, hi⟩
    have hmem' : i ∈ A.erase i := hsets ▸ hmem
    exact (Finset.mem_erase.mp hmem').1 rfl
  have hcross (i : V) (hi : i ∈ I) (q : V) (hq : q ∈ C) : i ≠ q := by
    intro heq
    subst q
    exact (Finset.disjoint_left.mp hCI) hq hi

  let pref : List V := [a, r d, b, r a, c, r b, d, r c]
  have hrowIndepNe (i j : V) (hi : i ∈ A) (hj : j ∈ A) : r i ≠ j := by
    intro heq
    exact hcross j (hAin hj) (r i) (hrows i hi).1 (by simpa [heq])
  have hrdra : r d ≠ r a := fun heq => had (hrowInj d a (by simp [A]) (by simp [A]) heq).symm
  have hrdrb : r d ≠ r b := fun heq => hbd (hrowInj d b (by simp [A]) (by simp [A]) heq).symm
  have hrdrc : r d ≠ r c := fun heq => hcd (hrowInj d c (by simp [A]) (by simp [A]) heq).symm
  have hrarb : r a ≠ r b := fun heq => hab (hrowInj a b (by simp [A]) (by simp [A]) heq)
  have hrarc : r a ≠ r c := fun heq => hac (hrowInj a c (by simp [A]) (by simp [A]) heq)
  have hrbrc : r b ≠ r c := fun heq => hbc (hrowInj b c (by simp [A]) (by simp [A]) heq)
  have hprefNodup : pref.Nodup := by
    have hrdB := hrowIndepNe d b (by simp [A]) (by simp [A])
    have hrdC := hrowIndepNe d c (by simp [A]) (by simp [A])
    have hrdD := hrowIndepNe d d (by simp [A]) (by simp [A])
    have haRd := (hrowIndepNe d a (by simp [A]) (by simp [A])).symm
    have haRa := (hrowIndepNe a a (by simp [A]) (by simp [A])).symm
    have haRb := (hrowIndepNe b a (by simp [A]) (by simp [A])).symm
    have haRc := (hrowIndepNe c a (by simp [A]) (by simp [A])).symm
    have hbRa := (hrowIndepNe a b (by simp [A]) (by simp [A])).symm
    have hbRb := (hrowIndepNe b b (by simp [A]) (by simp [A])).symm
    have hbRc := (hrowIndepNe c b (by simp [A]) (by simp [A])).symm
    have hcRb := (hrowIndepNe b c (by simp [A]) (by simp [A])).symm
    have hcRc := (hrowIndepNe c c (by simp [A]) (by simp [A])).symm
    have hdRc := (hrowIndepNe c d (by simp [A]) (by simp [A])).symm
    have hraC := hrowIndepNe a c (by simp [A]) (by simp [A])
    have hraD := hrowIndepNe a d (by simp [A]) (by simp [A])
    have hrbD := hrowIndepNe b d (by simp [A]) (by simp [A])
    simp [pref, hab, hac, had, hbc, hbd, hcd, hrdra, hrdrb, hrdrc,
      hrarb, hrarc, hrbrc, hrdB, hrdC, hrdD, hraC, hraD, hrbD,
      haRd, haRa, haRb, haRc, hbRa, hbRb, hbRc, hcRb, hcRc, hdRc]
  have hAdjRow (i j : V) (hi : i ∈ A) (hj : j ∈ A) (hne : i ≠ j) :
      G.Adj (r i) j := by
    have hjErase : j ∈ A.erase i := Finset.mem_erase.mpr ⟨(by intro h; exact hne h.symm), hj⟩
    have hjRow : j ∈ row G I (r i) := by rw [(hrows i hi).2]; exact hjErase
    change j ∈ I ∧ G.Adj (r i) j at hjRow
    exact hjRow.2
  have hAa : a ∈ A := by simp [A]
  have hAb : b ∈ A := by simp [A]
  have hAc : c ∈ A := by simp [A]
  have hAd : d ∈ A := by simp [A]
  have hrdA : G.Adj a (r d) := (hAdjRow d hAd hAa (by intro heq; exact had heq.symm)).symm
  have hrdB : G.Adj (r d) b := hAdjRow d hAd hAb (by intro h; exact hbd h.symm)
  have hraB : G.Adj b (r a) := (hAdjRow a hAa hAb (by intro heq; exact hab heq.symm)).symm
  have hraC : G.Adj (r a) c := hAdjRow a hAa hAc hac
  have hrbC : G.Adj c (r b) := (hAdjRow b hAb hAc (by intro heq; exact hbc heq.symm)).symm
  have hrbD : G.Adj (r b) d := hAdjRow b hAb hAd hbd
  have hrcD : G.Adj d (r c) := (hAdjRow c hAc hAd (by intro heq; exact hcd heq.symm)).symm
  have hprefChain : pref.IsChain G.Adj := by
    simp [pref, hrdA, hrdB, hraB, hraC, hrbC, hrbD, hrcD]
  have hprefLastC : ∀ x, x ∈ pref.getLast? → x ∈ C := by
    intro x hx
    simp [pref] at hx
    subst x
    exact (hrows c (by simp [A])).1
  let tail : List V := (C.filter fun x => x ∉ pref).toList
  have htailNodup : tail.Nodup := by simp [tail]
  have htailC : ∀ x ∈ tail, x ∈ C := by
    intro x hx
    exact (Finset.mem_filter.mp (Finset.mem_toList.mp hx)).1
  have hbaseTailDisjoint : ∀ x ∈ pref ++ [], x ∉ tail := by
    intro x hx htail
    exact (Finset.mem_filter.mp (Finset.mem_toList.mp htail)).2 hx
  have hcover : ∀ x : V, x ∈ pref ++ [] ∨ x ∈ tail := by
    intro x
    by_cases hp : x ∈ pref
    · exact Or.inl (List.mem_append_left [] hp)
    · have hx := Finset.mem_univ x
      rw [hpartition] at hx
      rcases Finset.mem_union.mp hx with hxC | hxI
      · exact Or.inr (Finset.mem_toList.mpr (Finset.mem_filter.mpr ⟨hxC, hp⟩))
      · have hxA : x ∈ A := hIeq ▸ hxI
        have hxA' : x = a ∨ x = b ∨ x = c ∨ x = d := by simpa [A] using hxA
        rcases hxA' with rfl | rfl | rfl | rfl <;> simp [pref] at hp
  have hprefNonempty : pref ++ [] ++ tail ≠ [] := by simp [pref]
  exact SplitGraphSmallRowsThree.hamiltonian_of_prefix_and_remaining_chain
    G C hC pref [] tail hprefNodup hprefChain hprefLastC
    (by simp) (by simp) (by simp) (by simp) (by simp)
    htailNodup htailC hbaseTailDisjoint hcover hprefNonempty

end SplitGraphKappaThreeFourTriples

#print axioms SplitGraphKappaThreeFourTriples.hamiltonian_of_all_four_triple_rows
