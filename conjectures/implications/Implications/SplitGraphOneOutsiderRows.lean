import Implications.SplitGraphComponents
import Implications.SplitGraphOneOutsider

/-!
Classify the two clique rows incident to a single outsider of a central triple.
-/

namespace SplitGraphOneOutsiderRows

variable {V : Type*} [DecidableEq V]

private theorem missing_from_pair (A P : Finset V) (hA : A.card = 3)
    (hPA : P ⊆ A) (hP : P.card = 2) :
    ∃ c, c ∈ A ∧ c ∉ P ∧ P = A.erase c := by
  have hcard : (A \ P).card = 1 := by
    rw [Finset.card_sdiff_of_subset hPA, hA, hP]
  obtain ⟨c, hc⟩ := Finset.card_eq_one.mp hcard
  have hmem : c ∈ A \ P := by rw [hc]; simp
  obtain ⟨hcA, hcP⟩ := Finset.mem_sdiff.mp hmem
  refine ⟨c, hcA, hcP, ?_⟩
  apply Finset.eq_of_subset_of_card_le
  · intro q hq
    exact Finset.mem_erase.mpr ⟨fun h => hcP (h ▸ hq), hPA hq⟩
  · rw [Finset.card_erase_of_mem hcA, hA, hP]

/-- Two distinct rows containing the only outsider each select a pair from the
central triple. Relabeling the triple gives the shared-pair or different-pair
incidence patterns. -/
theorem classify (I A B D : Finset V) (z : V)
    (hA : A.card = 3) (hI : I = insert z A) (hzA : z ∉ A)
    (hBI : B ⊆ I) (hDI : D ⊆ I)
    (hB : B.card ≤ 3) (hD : D.card ≤ 3)
    (hAB : (A \ B ∪ B \ A).card ≤ 2)
    (hAD : (A \ D ∪ D \ A).card ≤ 2)
    (hzB : z ∈ B) (hzD : z ∈ D) :
    ∃ a b c : V, a ≠ b ∧ a ≠ c ∧ b ≠ c ∧
      a ≠ z ∧ b ≠ z ∧ c ≠ z ∧ A = {a,b,c} ∧ I = {a,b,c,z} ∧
      B = {a,b,z} ∧ (D = {a,b,z} ∨ D = {a,c,z}) := by
  have hrow (P : Finset V) (hPI : P ⊆ I) (hzP : z ∈ P) :
      P = insert z (A ∩ P) := by
    ext q
    simp only [Finset.mem_insert, Finset.mem_inter]
    constructor
    · intro hq
      have hqI := hPI hq
      rw [hI, Finset.mem_insert] at hqI
      exact hqI.imp id fun h => ⟨h, hq⟩
    · rintro (rfl | ⟨_, hq⟩)
      · exact hzP
      · exact hq
  have hB2 := (SplitGraphComponents.tripleRow_outside_counts A B hA hB hAB
    ⟨z, Finset.mem_sdiff.mpr ⟨hzB, hzA⟩⟩).1
  have hD2 := (SplitGraphComponents.tripleRow_outside_counts A D hA hD hAD
    ⟨z, Finset.mem_sdiff.mpr ⟨hzD, hzA⟩⟩).1
  obtain ⟨c, hcA, _, hc⟩ := missing_from_pair A (A ∩ B) hA Finset.inter_subset_left hB2
  obtain ⟨b, hbA, _, hb⟩ := missing_from_pair A (A ∩ D) hA Finset.inter_subset_left hD2
  have hfinish (a b c : V) (haA : a ∈ A) (hbA : b ∈ A) (hcA : c ∈ A)
      (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
      (hABC : A = {a,b,c}) (hBpair : A ∩ B = {a,b})
      (hDpair : A ∩ D = {a,b} ∨ A ∩ D = {a,c}) :
      ∃ a b c : V, a ≠ b ∧ a ≠ c ∧ b ≠ c ∧
        a ≠ z ∧ b ≠ z ∧ c ≠ z ∧ A = {a,b,c} ∧ I = {a,b,c,z} ∧
        B = {a,b,z} ∧ (D = {a,b,z} ∨ D = {a,c,z}) := by
    have hne {v : V} (hv : v ∈ A) : v ≠ z := fun h => hzA (h ▸ hv)
    refine ⟨a,b,c,hab,hac,hbc,hne haA,hne hbA,hne hcA,hABC,?_,?_,?_⟩
    · rw [hI, hABC]
      ext q
      simp [or_comm, or_left_comm]
    · rw [hrow B hBI hzB, hBpair]
      ext q
      simp [or_comm, or_left_comm]
    · rw [hrow D hDI hzD]
      rcases hDpair with hp | hp
      · left
        rw [hp]
        ext q
        simp [or_comm, or_left_comm]
      · right
        rw [hp]
        ext q
        simp [or_comm, or_left_comm]
  by_cases hbc : b = c
  · obtain ⟨u, v, huv, huvp⟩ := Finset.card_eq_two.mp hB2
    have hu : u ∈ A.erase c := by rw [← hc, huvp]; simp
    have hv : v ∈ A.erase c := by rw [← hc, huvp]; simp
    obtain ⟨huc, huA⟩ := Finset.mem_erase.mp hu
    obtain ⟨hvc, hvA⟩ := Finset.mem_erase.mp hv
    have hAeq : A = {u,v,c} := by
      rw [← Finset.insert_erase hcA, ← hc, huvp]
      ext q
      simp [or_comm, or_left_comm]
    exact hfinish u v c huA hvA hcA huv huc hvc hAeq huvp
      (Or.inl (by rw [hb, hbc, ← hc, huvp]))
  · have hberase : b ∈ A.erase c := Finset.mem_erase.mpr ⟨hbc,hbA⟩
    have hacard : ((A.erase c).erase b).card = 1 := by
      rw [Finset.card_erase_of_mem hberase, Finset.card_erase_of_mem hcA, hA]
    obtain ⟨a, ha⟩ := Finset.card_eq_one.mp hacard
    have hamem : a ∈ (A.erase c).erase b := by rw [ha]; simp
    obtain ⟨hab, hac, haA⟩ := by
      simpa only [Finset.mem_erase, and_assoc] using hamem
    have hAeq : A = {a,b,c} := by
      rw [← Finset.insert_erase hcA, ← Finset.insert_erase hberase, ha]
      ext q
      simp [or_comm, or_left_comm]
    have hBpair : A ∩ B = {a,b} := by
      rw [hc, hAeq]
      ext q
      simp [and_or_left]
      grind
    have hDpair : A ∩ D = {a,c} := by
      rw [hb, hAeq]
      ext q
      simp [and_or_left]
      grind
    exact hfinish a b c haA hbA hcA hab hac hbc hAeq hBpair (Or.inr hDpair)

open SplitGraphTrees

/-- In the one-outsider case, the only remaining incidence pattern is the
different-pair case. Two attachments of the outsider supply the two rows. -/
theorem hamiltonian_of_one_outsider_of_different_pair
    [Fintype V] (G : SimpleGraph V) (C I : Finset V) (t z : V)
    (hC : G.IsClique (C : Set V)) (hdisj : Disjoint C I)
    (hpartition : (Finset.univ : Finset V) = C ∪ I)
    (ht : t ∈ C) (htriple : (row G I t).card = 3)
    (hI : I = insert z (row G I t)) (hz : z ∉ row G I t)
    (hsize : ∀ q ∈ C, (row G I q).card ≤ 3)
    (hdiff : ∀ q ∈ C, (rowDiff G I t q).card ≤ 2)
    (hdeg : ∀ i ∈ I, ∃ q ∈ C, ∃ d ∈ C, q ≠ d ∧ G.Adj q i ∧ G.Adj d i)
    (hdifferent : ∀ (a b c x y : V), a ≠ b → a ≠ c → b ≠ c →
      a ≠ z → b ≠ z → c ≠ z → x ∈ C → y ∈ C →
      t ≠ x → t ≠ y → x ≠ y →
      I = {a,b,c,z} → row G I t = {a,b,c} →
      row G I x = {a,b,z} → row G I y = {a,c,z} →
      ∃ (v w : V) (p : G.Walk v w), p.IsHamiltonian) :
    ∃ (v w : V) (p : G.Walk v w), p.IsHamiltonian := by
  classical
  have hzI : z ∈ I := by rw [hI]; simp
  obtain ⟨x, hx, y, hy, hxy, hxa, hya⟩ := hdeg z hzI
  have hzX : z ∈ row G I x := Finset.mem_filter.mpr ⟨hzI, hxa⟩
  have hzY : z ∈ row G I y := Finset.mem_filter.mpr ⟨hzI, hya⟩
  have htx : t ≠ x := fun h => hz (h.symm ▸ hzX)
  have hty : t ≠ y := fun h => hz (h.symm ▸ hzY)
  have hsub (q : V) : row G I q ⊆ I := Finset.filter_subset _ _
  obtain ⟨a,b,c,hab,hac,hbc,haz,hbz,hcz,hA,hI',hX,hY|hY⟩ :=
    classify I (row G I t) (row G I x) (row G I y) z htriple hI hz
      (hsub x) (hsub y) (hsize x hx) (hsize y hy) (hdiff x hx) (hdiff y hy) hzX hzY
  · exact SplitGraphOneOutsider.hamiltonian_of_one_outsider_shared_pair_rows
      G C I a b c z t x y hC hdisj hpartition hI' hab hac haz hbc hbz hcz
      ht hx hy htx hty hxy hA hX hY hdeg
  · exact hdifferent a b c x y hab hac hbc haz hbz hcz hx hy htx hty hxy hI' hA hX hY

end SplitGraphOneOutsiderRows

#print axioms SplitGraphOneOutsiderRows.classify
#print axioms SplitGraphOneOutsiderRows.hamiltonian_of_one_outsider_of_different_pair
