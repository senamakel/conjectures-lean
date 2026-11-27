import Implications.SplitGraphAttachments
import Implications.SplitGraphTrees

/-!
Hamiltonian paths through a central triple and at least two outsiders.
-/

namespace SplitGraphManyOutsiders

open SplitGraphTrees

variable {V : Type*} [Fintype V] [DecidableEq V]

omit [Fintype V] in
private theorem hamiltonian_of_list
    (G : SimpleGraph V) (l : List V) (hne : l ≠ []) (hnodup : l.Nodup)
    (hchain : l.IsChain G.Adj) (hcover : ∀ v : V, v ∈ l) :
    ∃ (u v : V) (p : G.Walk u v), p.IsHamiltonian := by
  classical
  let p := SimpleGraph.Walk.ofSupport l hne hchain
  have hpath : p.IsPath := by
    apply (SimpleGraph.Walk.isPath_def p).2
    simpa [p, SimpleGraph.Walk.support_ofSupport hne hchain] using hnodup
  have hvertices : ∀ v : V, v ∈ p.support := by
    intro v
    rw [SimpleGraph.Walk.support_ofSupport hne hchain]
    exact hcover v
  exact ⟨_, _, p, hpath.isHamiltonian_of_mem hvertices⟩

omit [Fintype V] in
/-- A list of distinct clique vertices is an adjacency chain. -/
private theorem clique_subset_list_chain (G : SimpleGraph V) (C : Finset V)
    (hC : G.IsClique (C : Set V)) (l : List V) (hnodup : l.Nodup)
    (hsub : ∀ x ∈ l, x ∈ C) : l.IsChain G.Adj := by
  rw [List.isChain_iff_forall_rel_of_append_cons_cons]
  intro x y l₁ l₂ heq
  have hx : x ∈ l := by rw [heq]; simp
  have hy : y ∈ l := by rw [heq]; simp
  have hxy : x ≠ y := by
    intro h
    subst y
    have hcount := (List.nodup_iff_count_le_one.mp hnodup) x
    rw [heq] at hcount
    simp [List.count_append] at hcount
    omega
  exact hC (hsub x hx) (hsub y hy) hxy

omit [Fintype V] [DecidableEq V] in
/-- Join a finite sequence of disjoint path blocks. The endpoints of each block
are in the clique, so the boundary relation is supplied by clique adjacency;
`List.isChain_flatten` then assembles the individual chains. Pairwise
disjointness of the blocks supplies nodup after flattening. -/
private theorem clique_ended_blocks
    (G : SimpleGraph V) (C : Finset V) (blocks : List (List V))
    (hC : G.IsClique (C : Set V))
    (hblocksNonempty : [] ∉ blocks)
    (hblockNodup : ∀ l ∈ blocks, l.Nodup)
    (hblocksDisjoint : blocks.Pairwise (fun l₁ l₂ => List.Disjoint l₁ l₂))
    (hblockChain : ∀ l ∈ blocks, l.IsChain G.Adj)
    (hboundary : blocks.IsChain (fun l₁ l₂ =>
      ∀ x ∈ l₁.getLast?, ∀ y ∈ l₂.head?,
        x ∈ C ∧ y ∈ C ∧ List.Disjoint l₁ l₂)) :
    blocks.flatten.Nodup ∧ blocks.flatten.IsChain G.Adj := by
  constructor
  · rw [List.nodup_flatten]
    exact ⟨hblockNodup, hblocksDisjoint⟩
  · rw [List.isChain_flatten hblocksNonempty]
    refine ⟨hblockChain, ?_⟩
    apply hboundary.imp_of_mem_imp
    intro l₁ l₂ hl₁ hl₂ hrel x hx y hy
    obtain ⟨hxC, hyC, hdisjoint⟩ := hrel x hx y hy
    apply hC hxC hyC
    intro hxy
    subst y
    exact (List.disjoint_left.mp hdisjoint)
      (List.mem_of_mem_getLast? hx) (List.mem_of_mem_head? hy)

omit [Fintype V] [DecidableEq V] in
/-- Append two disjoint path lists whose boundary vertices lie in the clique. -/
private theorem append_disjoint_clique_paths
    (G : SimpleGraph V) (C : Finset V) (hC : G.IsClique (C : Set V))
    (left right : List V) (hleftNodup : left.Nodup) (hrightNodup : right.Nodup)
    (hdisjoint : List.Disjoint left right)
    (hleftChain : left.IsChain G.Adj) (hrightChain : right.IsChain G.Adj)
    (hleftEnd : ∀ x ∈ left.getLast?, x ∈ C)
    (hrightStart : ∀ y ∈ right.head?, y ∈ C) :
    (left ++ right).Nodup ∧ (left ++ right).IsChain G.Adj := by
  constructor
  · rw [List.nodup_append']
    exact ⟨hleftNodup, hrightNodup, (List.disjoint_left.mp hdisjoint)⟩
  · rw [List.isChain_append]
    refine ⟨hleftChain, hrightChain, ?_⟩
    intro x hx y hy
    have hxy : x ≠ y := by
      intro h
      exact (List.disjoint_left.mp hdisjoint)
        (List.mem_of_mem_getLast? hx) (h ▸ List.mem_of_mem_head? hy)
    exact hC (hleftEnd x hx) (hrightStart y hy) hxy

omit [Fintype V] in
/-- The globally chosen attachments produce pairwise disjoint three-vertex
outsider blocks, so flattening the blocks cannot repeat a vertex. -/
private theorem outsider_blocks_nodup
    (G : SimpleGraph V) (C I : Finset V) (t : V)
    (hdisj : Disjoint C I)
    (indices : List ↥(I \ row G I t)) (hindices : indices.Nodup)
    (f : ((I \ row G I t : Finset V) × Bool) ↪ (C.erase t : Finset V)) :
    ( indices.flatMap fun i =>
      [((f (i, false) : C.erase t) : V), (i : V),
        ((f (i, true) : C.erase t) : V)] ).Nodup ∧
      (indices.map fun i =>
        [((f (i, false) : C.erase t) : V), (i : V),
          ((f (i, true) : C.erase t) : V)]).Pairwise List.Disjoint ∧
      (indices.map fun i =>
        [((f (i, false) : C.erase t) : V), (i : V),
          ((f (i, true) : C.erase t) : V)]).Pairwise (fun l₁ l₂ =>
            ∀ x ∈ l₁.getLast?, ∀ y ∈ l₂.head?,
              x ∈ C ∧ y ∈ C ∧ List.Disjoint l₁ l₂) := by
  classical
  let O := I \ row G I t
  let block (i : O) : List V :=
    [((f (i, false) : C.erase t) : V), (i : V),
      ((f (i, true) : C.erase t) : V)]
  have hcenterC (i : O) (b : Bool) : (f (i, b) : V) ∈ C := by
    exact (Finset.mem_erase.mp (f (i, b)).property).2
  have hcenterNotI (i : O) (b : Bool) : (f (i, b) : V) ∉ I := by
    intro hi
    exact (Finset.disjoint_left.mp hdisj) (hcenterC i b) hi
  have hcenterNotOut (i j : O) (b : Bool) : (f (i, b) : V) ≠ j := by
    intro h
    exact hcenterNotI i b (h ▸ (Finset.mem_sdiff.mp j.property).1)
  have hblockNodup (i : O) : (block i).Nodup := by
    have hxy : (f (i, false) : V) ≠ f (i, true) := by
      intro h
      have hf := f.injective (Subtype.ext h)
      exact Bool.noConfusion (congrArg Prod.snd hf)
    have hxi : (f (i, false) : V) ≠ i := by
      exact fun h => hcenterNotI i false (h ▸ (Finset.mem_sdiff.mp i.property).1)
    have hiy : (i : V) ≠ f (i, true) := by
      exact fun h => hcenterNotI i true (h.symm ▸ (Finset.mem_sdiff.mp i.property).1)
    simp [block, hxy, hxi, hiy]
  have hblocksDisjoint (i j : O) (hij : i ≠ j) : List.Disjoint (block i) (block j) := by
    rw [List.disjoint_left]
    intro q hqi hqj
    simp only [block, List.mem_cons, List.not_mem_nil, or_false] at hqi hqj
    rcases hqi with hiX | hi | hiY
    · rcases hqj with hjX | hj | hjY
      · have hf := f.injective (Subtype.ext (hiX.symm.trans hjX))
        apply hij
        apply Subtype.ext
        exact congrArg Subtype.val (congrArg Prod.fst hf)
      · exact hcenterNotOut i j false (hiX.symm.trans hj)
      · have hf := f.injective (Subtype.ext (hiX.symm.trans hjY))
        exact Bool.noConfusion (congrArg Prod.snd hf)
    · rcases hqj with hjX | hj | hjY
      · exact hcenterNotOut j i false (hjX.symm.trans hi)
      · apply hij
        apply Subtype.ext
        exact hi.symm.trans hj
      · exact hcenterNotOut j i true (hjY.symm.trans hi)
    · rcases hqj with hjX | hj | hjY
      · have hf := f.injective (Subtype.ext (hiY.symm.trans hjX))
        exact Bool.noConfusion (congrArg Prod.snd hf)
      · exact hcenterNotOut i j true (hiY.symm.trans hj)
      · have hf := f.injective (Subtype.ext (hiY.symm.trans hjY))
        apply hij
        apply Subtype.ext
        exact congrArg Subtype.val (congrArg Prod.fst hf)
  have hpair : indices.Pairwise (fun i j => List.Disjoint (block i) (block j)) :=
    hindices.imp (by
      intro i j hij
      exact hblocksDisjoint i j hij)
  have hboundaryPair : indices.Pairwise (fun i j =>
      ∀ x ∈ (block i).getLast?, ∀ y ∈ (block j).head?,
        x ∈ C ∧ y ∈ C ∧ List.Disjoint (block i) (block j)) :=
    hindices.imp (by
      intro i j hij x hx y hy
      have hx' : x = (f (i, true) : V) := by simpa [block] using hx.symm
      have hy' : y = (f (j, false) : V) := by simpa [block] using hy.symm
      subst x
      subst y
      exact ⟨hcenterC i true, hcenterC j false, hblocksDisjoint i j hij⟩)
  have hflat : (indices.flatMap block).Nodup := by
    rw [List.nodup_flatMap]
    exact ⟨(by intro i hi; exact hblockNodup i), hpair⟩
  refine ⟨?_, ?_⟩
  · simpa [O, block] using hflat
  · refine ⟨?_, ?_⟩
    · simpa [O, block] using (List.pairwise_map.mpr hpair)
    · simpa [O, block] using (List.pairwise_map.mpr hboundaryPair)

omit [Fintype V] in
/-- The attachment embedding turns the outsiders into a chain of disjoint
three-vertex blocks whose endpoints lie in the clique. -/
private theorem outsider_blocks_chain
    (G : SimpleGraph V) (C I : Finset V) (t : V)
    (hC : G.IsClique (C : Set V)) (hdisj : Disjoint C I)
    (indices : List ↥(I \ row G I t)) (hindices : indices.Nodup)
    (f : ((I \ row G I t : Finset V) × Bool) ↪ (C.erase t : Finset V))
    (hattach : ∀ i b, G.Adj (f (i, b) : V) (i : V)) :
    (indices.flatMap fun i =>
      [((f (i, false) : C.erase t) : V), (i : V),
        ((f (i, true) : C.erase t) : V)]).Nodup ∧
    (indices.flatMap fun i =>
      [((f (i, false) : C.erase t) : V), (i : V),
        ((f (i, true) : C.erase t) : V)]).IsChain G.Adj := by
  classical
  let O := I \ row G I t
  let block (i : O) : List V :=
    [((f (i, false) : C.erase t) : V), (i : V),
      ((f (i, true) : C.erase t) : V)]
  let blocks := indices.map block
  have hdata := outsider_blocks_nodup G C I t hdisj indices hindices f
  have hflatNodup : blocks.flatten.Nodup := by
    change (indices.flatMap block).Nodup
    simpa [O, block] using hdata.1
  have hblockNodup : ∀ l ∈ blocks, l.Nodup := (List.nodup_flatten.mp hflatNodup).1
  have hblocksDisjoint : blocks.Pairwise List.Disjoint := (List.nodup_flatten.mp hflatNodup).2
  have hblockChain : ∀ l ∈ blocks, l.IsChain G.Adj := by
    intro l hl
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hl
    simp only [block, List.isChain_cons_cons, List.isChain_singleton]
    exact ⟨hattach i false, ⟨(hattach i true).symm, trivial⟩⟩
  have hboundaryPair : blocks.Pairwise (fun l₁ l₂ =>
      ∀ x ∈ l₁.getLast?, ∀ y ∈ l₂.head?,
        x ∈ C ∧ y ∈ C ∧ List.Disjoint l₁ l₂) := by
    simpa [blocks, block, O, List.pairwise_map] using hdata.2.2
  have hboundary := hboundaryPair.isChain
  have hnonempty : [] ∉ blocks := by
    simp [blocks, block]
  have hjoined := clique_ended_blocks G C blocks hC hnonempty hblockNodup
    hblocksDisjoint hblockChain hboundary
  change (indices.flatMap block).Nodup ∧
    (indices.flatMap block).IsChain G.Adj at hjoined
  simpa [O, block] using hjoined

/-- A triple row with at least two outsiders has a common attached pair: every
clique row meeting the outside contains the same two vertices of the triple. -/
private theorem triple_row_common_pair_for_many_outsiders
    (G : SimpleGraph V) (C I : Finset V) (t : V)
    (ht : t ∈ C) (hA : (row G I t).card = 3)
    (houts : 2 ≤ (I \ row G I t).card)
    (hrow : ∀ q ∈ C, (row G I q).card ≤ 3)
    (hdiff : ∀ q ∈ C, ∀ d ∈ C, q ≠ d → (rowDiff G I q d).card ≤ 2)
    (hdeg : ∀ i ∈ I, ∃ q ∈ C, ∃ d ∈ C, q ≠ d ∧ G.Adj q i ∧ G.Adj d i) :
    ∃ a b c, a ≠ b ∧ a ≠ c ∧ b ≠ c ∧ row G I t = {a, b, c} ∧
      ∀ i ∈ I \ row G I t, ∀ q ∈ C, G.Adj q i →
        a ∈ row G I q ∧ b ∈ row G I q := by
  classical
  let A := row G I t
  let O := I \ A
  have hOC : 2 ≤ O.card := by simpa [O, A] using houts
  obtain ⟨z, hzO, w, hwO, hzw⟩ := Finset.one_lt_card.mp (by omega : 1 < O.card)
  obtain ⟨f, hfadj⟩ :=
    _root_.Implications.SplitGraphAttachments.exists_outsider_attachments
      G C I t ht hA hrow hdiff hdeg
  have hRsize : ∀ B ∈ C.image (row G I), B.card ≤ 3 := by
    intro B hB
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hB
    exact hrow q hq
  have hRdiff : ∀ B ∈ C.image (row G I), ∀ D ∈ C.image (row G I),
      (B \ D ∪ D \ B).card ≤ 2 := by
    intro B hB D hD
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hB
    obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hD
    by_cases hqd : q = d
    · subst d
      simp
    · simpa [rowDiff] using hdiff q hq d hd hqd
  have hAR : A ∈ C.image (row G I) := Finset.mem_image.mpr ⟨t, ht, rfl⟩
  let iz : O := ⟨z, hzO⟩
  let iw : O := ⟨w, hwO⟩
  let x : V := f (iz, false)
  let r : V := f (iw, false)
  have hxC : x ∈ C := (Finset.mem_erase.mp (f (iz, false)).property).2
  have hrC : r ∈ C := (Finset.mem_erase.mp (f (iw, false)).property).2
  have hzI : z ∈ I := (Finset.mem_sdiff.mp hzO).1
  have hwI : w ∈ I := (Finset.mem_sdiff.mp hwO).1
  have hzA : z ∉ A := (Finset.mem_sdiff.mp hzO).2
  have hwA : w ∉ A := (Finset.mem_sdiff.mp hwO).2
  have hxR : row G I x ∈ C.image (row G I) := Finset.mem_image.mpr ⟨x, hxC, rfl⟩
  have hrR : row G I r ∈ C.image (row G I) := Finset.mem_image.mpr ⟨r, hrC, rfl⟩
  have hxz : G.Adj x z := hfadj iz false
  have hrw : G.Adj r w := hfadj iw false
  have hzRow : z ∈ row G I x \ A :=
    Finset.mem_sdiff.mpr ⟨Finset.mem_filter.mpr ⟨hzI, hxz⟩, hzA⟩
  have hwRow : w ∈ row G I r \ A :=
    Finset.mem_sdiff.mpr ⟨Finset.mem_filter.mpr ⟨hwI, hrw⟩, hwA⟩
  obtain ⟨P, hPA, hPcard, hcommon⟩ :=
    SplitGraphComponents.tripleRow_common_outside_pair A (C.image (row G I))
      hA hAR hRsize hRdiff hxR hrR hzRow hwRow hzw
  obtain ⟨a, b, hab, hPeq⟩ := Finset.card_eq_two.mp hPcard
  have hdiffCard : (A \ P).card = 1 := by
    have hcard := Finset.card_sdiff_add_card_inter A P
    rw [Finset.inter_eq_right.mpr hPA, hA, hPcard] at hcard
    omega
  obtain ⟨c, hcDiffEq⟩ := Finset.card_eq_one.mp hdiffCard
  have hcDiff : c ∈ A \ P := by rw [hcDiffEq]; simp
  have hcA : c ∈ A := (Finset.mem_sdiff.mp hcDiff).1
  have hcP : c ∉ P := (Finset.mem_sdiff.mp hcDiff).2
  have hac : a ≠ c := by intro h; subst c; exact hcP (by rw [hPeq]; simp)
  have hbc : b ≠ c := by intro h; subst c; exact hcP (by rw [hPeq]; simp)
  have hAeq : A = {a, b, c} := by
    apply Finset.eq_of_subset_of_card_le
    · intro q hq
      by_cases hqP : q ∈ P
      · rw [hPeq] at hqP
        have hqAB : q = a ∨ q = b := by simpa using hqP
        rcases hqAB with hqa | hqb
        · simp [hqa]
        · simp [hqb]
      · have hqDiff : q ∈ A \ P := Finset.mem_sdiff.mpr ⟨hq, hqP⟩
        rw [hcDiffEq] at hqDiff
        simp only [Finset.mem_singleton] at hqDiff
        simp [hqDiff]
    · have hcardABC : ({a, b, c} : Finset V).card = 3 := by simp [hab, hac, hbc]
      rw [hA]
      exact hcardABC.le
  have hcomm (q : V) (hq : q ∈ C) (hout : (row G I q \ A).Nonempty) :
      A ∩ row G I q = P :=
    hcommon (row G I q) (Finset.mem_image.mpr ⟨q, hq, rfl⟩) hout
  refine ⟨a, b, c, hab, hac, hbc, hAeq, ?_⟩
  intro i hi q hq hadj
  have houtside : i ∈ row G I q \ A := by
    refine Finset.mem_sdiff.mpr ⟨Finset.mem_filter.mpr ?_, (Finset.mem_sdiff.mp hi).2⟩
    exact ⟨(Finset.mem_sdiff.mp hi).1, hadj⟩
  have hEq := hcomm q hq ⟨i, houtside⟩
  constructor
  · have : a ∈ A ∩ row G I q := by rw [hEq, hPeq]; simp
    exact (Finset.mem_inter.mp this).2
  · have : b ∈ A ∩ row G I q := by rw [hEq, hPeq]; simp
    exact (Finset.mem_inter.mp this).2

 /-- With at least two outsiders, insert one common-pair vertex before the
first outsider block and the other between the first and second blocks. -/
theorem hamiltonian_of_many_outsiders
    (G : SimpleGraph V) (C I : Finset V) (t : V)
    (hC : G.IsClique (C : Set V)) (hdisj : Disjoint C I)
    (hpartition : (Finset.univ : Finset V) = C ∪ I)
    (ht : t ∈ C) (hA : (row G I t).card = 3)
    (houts : 2 ≤ (I \ row G I t).card)
    (hrow : ∀ q ∈ C, (row G I q).card ≤ 3)
    (hdiff : ∀ q ∈ C, ∀ d ∈ C, q ≠ d → (rowDiff G I q d).card ≤ 2)
    (hdeg : ∀ i ∈ I, ∃ q ∈ C, ∃ d ∈ C, q ≠ d ∧ G.Adj q i ∧ G.Adj d i) :
    ∃ (v w : V) (p : G.Walk v w), p.IsHamiltonian := by
  classical
  let A := row G I t
  let O := I \ A
  obtain ⟨a, b, c, hab, hac, hbc, hAeq, hpair⟩ :=
    triple_row_common_pair_for_many_outsiders G C I t ht hA houts hrow hdiff hdeg
  have ha : a ∈ A := by simp [A, hAeq]
  have hb : b ∈ A := by simp [A, hAeq]
  have hc : c ∈ A := by simp [A, hAeq]
  have hAI : A ⊆ I := Finset.filter_subset _ _
  have hne {q : V} (hq : q ∈ I) : t ≠ q :=
    fun h => (Finset.disjoint_left.mp hdisj) ht (h.symm ▸ hq)
  obtain ⟨f, hf⟩ := Implications.SplitGraphAttachments.exists_outsider_attachments
    G C I t ht hA hrow hdiff hdeg
  let block (k : O) : List V := [f (k,false), k, f (k,true)]
  have hFC (k : O) (e : Bool) : (f (k,e) : V) ∈ C :=
    (Finset.mem_erase.mp (f (k,e)).property).2
  have hFt (k : O) (e : Bool) : (f (k,e) : V) ≠ t :=
    (Finset.mem_erase.mp (f (k,e)).property).1
  have hOI (k : O) : (k : V) ∈ I := (Finset.mem_sdiff.mp k.property).1
  have hOA (k : O) : (k : V) ∉ A := (Finset.mem_sdiff.mp k.property).2
  have hlen : 2 ≤ O.attach.toList.length := by simpa [O, A] using houts
  obtain ⟨i, j, is, hindices⟩ : ∃ i j : O, ∃ is : List O,
      O.attach.toList = i :: j :: is := by
    cases hs : O.attach.toList with
    | nil => simp [hs] at hlen
    | cons i tail =>
      cases tail with
      | nil => simp [hs] at hlen
      | cons j is => exact ⟨i,j,is,rfl⟩
  have hindexNodup : (i :: j :: is).Nodup := hindices ▸ Finset.nodup_toList O.attach
  let more := (j :: is).flatMap block
  let flat := block i ++ more
  have hflat : flat.Nodup := (outsider_blocks_chain G C I t hC hdisj (i :: j :: is)
    hindexNodup f hf).1
  have hmore : more.Nodup ∧ more.IsChain G.Adj :=
    outsider_blocks_chain G C I t hC hdisj (j :: is) hindexNodup.of_cons f hf
  have hflat_cases {q : V} (hq : q ∈ flat) :
      (q ∈ C ∧ q ≠ t) ∨ q ∈ O := by
    change q ∈ (i :: j :: is).flatMap block at hq
    obtain ⟨k, _, hk⟩ := List.mem_flatMap.mp hq
    simp only [block, List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with rfl | rfl | rfl
    · exact Or.inl ⟨hFC k false, hFt k false⟩
    · exact Or.inr k.property
    · exact Or.inl ⟨hFC k true, hFt k true⟩
  have hOflat {q : V} (hq : q ∈ O) : q ∈ flat := by
    let k : O := ⟨q,hq⟩
    have hk : k ∈ O.attach.toList := Finset.mem_toList.mpr (Finset.mem_attach _ _)
    rw [hindices] at hk
    change q ∈ (i :: j :: is).flatMap block
    exact List.mem_flatMap.mpr ⟨k,hk,by simp [block,k]⟩
  let D := C.filter fun q => q ≠ t ∧ q ∉ flat
  let spare := D.toList
  have hspare {q : V} : q ∈ spare ↔ q ∈ C ∧ q ≠ t ∧ q ∉ flat := by
    simp [spare,D]
  have hspareN : spare.Nodup := Finset.nodup_toList D
  have hspareChain := clique_subset_list_chain G C hC spare hspareN (fun q hq => (hspare.mp hq).1)
  have htailEnd (ks : List O) : ∀ q ∈ (ks.flatMap block).getLast?, q ∈ C := by
    induction ks with
    | nil => simp
    | cons k ks ih =>
      cases ks with
      | nil =>
        intro q hq
        simp [block] at hq
        exact hq ▸ hFC k true
      | cons m ms =>
        intro q hq
        simp only [List.flatMap_cons, List.getLast?_append_of_ne_nil _
          (by simp [block] : block m ++ ms.flatMap block ≠ [])] at hq
        exact ih q hq
  have htail : (more ++ spare).Nodup ∧ (more ++ spare).IsChain G.Adj :=
    append_disjoint_clique_paths G C hC more spare hmore.1 hspareN
      (List.disjoint_left.mpr (fun q hq hs => (hspare.mp hs).2.2 (List.mem_append_right _ hq)))
      hmore.2 hspareChain (htailEnd (j :: is))
      (fun q hq => (hspare.mp (List.mem_of_mem_head? hq)).1)
  let fixed := [c,t,a,b]
  have hfixed : fixed.Nodup := by
    simp [fixed, hab, hac.symm, hbc.symm, hne (hAI ha), hne (hAI hb), (hne (hAI hc)).symm]
  have hfixed_cases {q : V} (hq : q ∈ fixed) : q = t ∨ q ∈ A := by
    simp [fixed,A,hAeq] at hq ⊢
    tauto
  have hfixedFlat : List.Disjoint fixed flat := by
    refine List.disjoint_left.mpr (fun q hq hqf => ?_)
    rcases hfixed_cases hq with rfl | hqA
    · rcases hflat_cases hqf with ⟨_,h⟩ | ho
      · exact h rfl
      · exact (Finset.disjoint_left.mp hdisj) ht (Finset.mem_sdiff.mp ho).1
    · rcases hflat_cases hqf with ⟨hqC,_⟩ | ho
      · exact (Finset.disjoint_left.mp hdisj) hqC (hAI hqA)
      · exact (Finset.mem_sdiff.mp ho).2 hqA
  have hbaseline : (fixed ++ flat ++ spare).Nodup := by
    refine List.Nodup.append (List.Nodup.append hfixed hflat hfixedFlat) hspareN ?_
    refine List.disjoint_left.mpr (fun q hq hs => ?_)
    obtain ⟨hqC,hqt,hqf⟩ := hspare.mp hs
    rcases List.mem_append.mp hq with hfixed' | hflat'
    · rcases hfixed_cases hfixed' with rfl | hqA
      · exact hqt rfl
      · exact (Finset.disjoint_left.mp hdisj) hqC (hAI hqA)
    · exact hqf hflat'
  have hbaselineCover (q : V) : q ∈ fixed ++ flat ++ spare := by
    have hq := Finset.mem_univ q
    rw [hpartition] at hq
    rcases Finset.mem_union.mp hq with hqC | hqI
    · by_cases hqt : q = t
      · simp [fixed,hqt]
      · by_cases hqf : q ∈ flat
        · simp [hqf]
        · exact List.mem_append_right _ (hspare.mpr ⟨hqC,hqt,hqf⟩)
    · by_cases hqA : q ∈ A
      · have hqFix : q ∈ fixed := by
          simp [fixed,A,hAeq] at hqA ⊢
          tauto
        exact List.mem_append_left _ (List.mem_append_left _ hqFix)
      · have hqf := hOflat (Finset.mem_sdiff.mpr ⟨hqI,hqA⟩)
        simp [hqf]
  let ahead := [c,t,a]
  let lead := ahead ++ block i ++ [b]
  let path := lead ++ (more ++ spare)
  have hmove : path.Perm (fixed ++ flat ++ spare) := by
    have hp : (block i ++ b :: more).Perm (b :: (block i ++ more)) := List.perm_middle
    convert (hp.append_left ahead).append_right spare using 1 <;>
      simp [path, lead, ahead, fixed, flat, List.append_assoc]
  have hta : G.Adj t a := (Finset.mem_filter.mp ha).2
  have htc : G.Adj t c := (Finset.mem_filter.mp hc).2
  have hia : G.Adj (f (i,false) : V) a :=
    (Finset.mem_filter.mp (hpair i i.property _ (hFC i false) (hf i false)).1).2
  have hib : G.Adj (f (i,true) : V) b :=
    (Finset.mem_filter.mp (hpair i i.property _ (hFC i true) (hf i true)).2).2
  have hjb : G.Adj (f (j,false) : V) b :=
    (Finset.mem_filter.mp (hpair j j.property _ (hFC j false) (hf j false)).2).2
  have hlead : lead.IsChain G.Adj := by
    simp [lead, ahead, block, List.isChain_cons, htc.symm, hta, hia.symm, hf i false,
      (hf i true).symm, hib]
  have hchain : path.IsChain G.Adj := by
    apply List.IsChain.append hlead htail.2
    intro q hq r hr
    have hqb : q = b := by simpa [lead, ahead, block] using hq.symm
    have hrj : r = f (j,false) := by simpa [more, block] using hr.symm
    simpa [hqb,hrj] using hjb.symm
  exact hamiltonian_of_list G path (by simp [path, lead, ahead]) (hmove.nodup_iff.mpr hbaseline)
    hchain (fun q => hmove.mem_iff.mpr (hbaselineCover q))

end SplitGraphManyOutsiders

#print axioms SplitGraphManyOutsiders.hamiltonian_of_many_outsiders
