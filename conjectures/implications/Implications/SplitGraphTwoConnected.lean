import Mathlib

/-!
Deletion connectivity supplies the attachments needed by the split-graph path
construction.
-/

namespace SplitGraphTwoConnected

variable {V : Type*} [Fintype V] [DecidableEq V]

private theorem exists_neighbor_avoiding
    (G : SimpleGraph V) (hcard : 3 ≤ Fintype.card V)
    (v q : V) (hvq : v ≠ q)
    (hconn : (G.induce {x | x ≠ q}).Connected) :
    ∃ w : V, w ≠ q ∧ G.Adj w v := by
  classical
  let D := (Finset.univ.erase q).erase v
  have hv : v ∈ (Finset.univ : Finset V).erase q := by simp [hvq]
  have hd : D.card = Fintype.card V - 1 - 1 := by
    dsimp [D]
    rw [Finset.card_erase_of_mem hv, Finset.card_erase_of_mem (Finset.mem_univ q),
      Finset.card_univ]
  obtain ⟨d, hdD⟩ := Finset.card_pos.mp (show 0 < D.card by omega)
  obtain ⟨hdv, hdq⟩ := Finset.mem_erase.mp hdD
  have hdq := (Finset.mem_erase.mp hdq).1
  let v' : {x : V | x ≠ q} := ⟨v, hvq⟩
  let d' : {x : V | x ≠ q} := ⟨d, hdq⟩
  have hvd : v' ≠ d' := fun h => hdv (congrArg Subtype.val h).symm
  obtain ⟨p, _⟩ := (hconn.preconnected v' d').exists_isPath
  exact ⟨p.snd.val, p.snd.property, (p.adj_snd (p.not_nil_of_ne hvd)).symm⟩

/-- In a graph of order at least three that remains connected after every
single-vertex deletion, each independent-side vertex has two clique neighbors. -/
theorem two_attachments_of_deletion_connected
    (G : SimpleGraph V) (C I : Finset V)
    (hI : G.IsIndepSet (I : Set V))
    (hpartition : (Finset.univ : Finset V) = C ∪ I)
    (hcard : 3 ≤ Fintype.card V)
    (hconn : ∀ q : V, (G.induce {x | x ≠ q}).Connected) :
    ∀ i ∈ I, ∃ q ∈ C, ∃ d ∈ C, q ≠ d ∧ G.Adj q i ∧ G.Adj d i := by
  classical
  have : Nontrivial V := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  intro i hi
  have htoC (w : V) (hw : G.Adj w i) : w ∈ C := by
    have hwi : w ≠ i := hw.ne
    have hwU := Finset.mem_univ w
    rw [hpartition] at hwU
    exact (Finset.mem_union.mp hwU).resolve_right
      (fun hwI => hI hwI hi hwi hw)
  obtain ⟨x, hxi⟩ := exists_ne i
  obtain ⟨q, _, hqi⟩ := exists_neighbor_avoiding G hcard i x hxi.symm (hconn x)
  obtain ⟨d, hdq, hdi⟩ := exists_neighbor_avoiding G hcard i q hqi.ne.symm (hconn q)
  exact ⟨q, htoC q hqi, d, htoC d hdi, hdq.symm, hqi, hdi⟩

end SplitGraphTwoConnected

#print axioms SplitGraphTwoConnected.two_attachments_of_deletion_connected
