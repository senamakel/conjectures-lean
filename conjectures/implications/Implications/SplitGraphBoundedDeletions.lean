import Implications.SplitGraphTrees

/-! Connectivity supplies the column bounds for a split-graph incidence cut. -/

namespace SplitGraphBoundedDeletions

variable {V : Type*} [DecidableEq V]

/-- If deleting at most `k - 1` vertices always leaves a connected graph,
every independent-side vertex has at least `k` neighbors in the clique. -/
theorem attachment_count_of_bounded_deletion_connected [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (C I : Finset V) (k : ℕ)
    (hI : G.IsIndepSet (I : Set V))
    (hpartition : (Finset.univ : Finset V) = C ∪ I)
    (hcard : k + 1 ≤ Fintype.card V)
    (hconn : ∀ D : Finset V, D.card < k → (G.induce {x | x ∉ D}).Connected) :
    ∀ i ∈ I, k ≤ (C.filter fun v => G.Adj v i).card := by
  classical
  intro i hi
  let N := C.filter fun v => G.Adj v i
  change k ≤ N.card
  by_contra! hsmall
  have hiN : i ∉ N := by
    intro hin
    exact G.irrefl (Finset.mem_filter.mp hin).2
  let R : Finset V := Finset.univ \ N
  have hiR : i ∈ R := Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hiN⟩
  have hR : R.card = Fintype.card V - N.card := by
    change (Finset.univ \ N).card = _
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ N), Finset.card_univ]
  have hT : 0 < (R.erase i).card := by
    rw [Finset.card_erase_of_mem hiR, hR]
    omega
  obtain ⟨d, hd⟩ := Finset.card_pos.mp hT
  have hdi := (Finset.mem_erase.mp hd).1
  have hdN := (Finset.mem_sdiff.mp (Finset.mem_erase.mp hd).2).2
  let i' : {x : V | x ∉ N} := ⟨i, hiN⟩
  let d' : {x : V | x ∉ N} := ⟨d, hdN⟩
  have hne : i' ≠ d' := fun he => hdi (congrArg Subtype.val he).symm
  obtain ⟨p, _⟩ := ((hconn N hsmall).preconnected i' d').exists_isPath
  have hwAdj : G.Adj p.snd.val i := (p.adj_snd (p.not_nil_of_ne hne)).symm
  have hwI : p.snd.val ∉ I := fun hw => hI hw hi hwAdj.ne hwAdj
  have hwC : p.snd.val ∈ C := by
    have hw := Finset.mem_univ p.snd.val
    rw [hpartition] at hw
    exact (Finset.mem_union.mp hw).resolve_right hwI
  exact p.snd.property (Finset.mem_filter.mpr ⟨hwC, hwAdj⟩)

/-- The row and row-difference bounds still hold after restricting the
independent side to an arbitrary subset, as required by a flow cut. -/
theorem restricted_row_bounds
    (G : SimpleGraph V) (C I S : Finset V) (k : ℕ)
    (hS : S ⊆ I) (hTree : SplitGraphTrees.inducedTreeBound G k)
    (hC : G.IsClique (C : Set V)) (hI : G.IsIndepSet (I : Set V))
    (hCI : Disjoint C I) :
    (∀ c ∈ C, (SplitGraphTrees.row G S c).card ≤ k + 1) ∧
      (∀ c ∈ C, ∀ d ∈ C, c ≠ d → (SplitGraphTrees.rowDiff G S c d).card ≤ k) := by
  classical
  have ⟨hrows, hdiff⟩ := SplitGraphTrees.rows_bounded_of_inducedTreeBound G C I k hTree hC hI hCI
  constructor
  · intro c hc
    apply le_trans (Finset.card_le_card _) (hrows c hc)
    intro x hx
    change x ∈ S.filter (fun v => G.Adj c v) at hx
    change x ∈ I.filter (fun v => G.Adj c v)
    exact Finset.mem_filter.mpr ⟨hS (Finset.mem_filter.mp hx).1, (Finset.mem_filter.mp hx).2⟩
  · intro c hc d hd hcd
    apply le_trans (Finset.card_le_card _) (hdiff c hc d hd hcd)
    intro x hx
    rw [SplitGraphTrees.mem_rowDiff_iff] at hx ⊢
    exact ⟨hS hx.1, hx.2⟩

#print axioms attachment_count_of_bounded_deletion_connected
#print axioms restricted_row_bounds

end SplitGraphBoundedDeletions
