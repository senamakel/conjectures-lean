import Implications.C4PolarityCounterAssignment
import Implications.C4PolarityEncoderInputs
import Implications.C4PolarityLexEncoding
import Implications.C4PolarityLratBridge

open C4PolarityOrderSeven
open Implications.C4PolarityCounterAssignment Implications.C4PolarityEncoderInputs
open Implications.C4PolarityEdgeEncoding Implications.C4PolarityLexEncoding


/-! The order-seven polarity clause list used by the certificate replay. -/

namespace Implications.C4PolarityCertifiedFormula

open C4PolarityDimacs C4PolarityLratBridge C4PolarityThresholdEncoding

/-- Adjacency list in the same order as the encoder's scan of all vertices. -/
def neighborList (i : Fin 57) : List (Fin 57) :=
  (List.finRange 57).filter fun j => decide (i ≠ j ∧ orthogonal i j)

def survivorClauses : List (List Int) :=
  (List.finRange 57).flatMap fun i =>
    let neighbors := neighborList i
    (neighbors.sublistsLen (neighbors.length - 5)).reverse.map fun excess =>
      (deletionId i : Int) :: excess.map fun j => -(deletionId j : Int)

def deletionVariables : List Nat :=
  (List.finRange 57).map deletionId

def instanceClauses (permutations : List (List Nat)) : List (List Int) :=
  [[1]] ++ numberedCounter 58 16 (deletionVariables.map Int.ofNat) ++ [[969], [-970]] ++
    edgeFormula orthogonalPairs ++ numberedCounter 1194 34 scoreDimacsInputs ++ [[9082]] ++
    survivorClauses ++ orbitLexClauses 1 9083 deletionVariables permutations

private theorem neighborList_toFinset (i : Fin 57) :
    (neighborList i).toFinset = graph.neighborFinset i := by
  ext j
  simp [neighborList]; rfl

private theorem neighborList_nodup (i : Fin 57) : (neighborList i).Nodup :=
  (List.nodup_finRange 57).filter _

/-- Every survivor clause in the concrete reconstruction is satisfied by a
candidate's deletion bits, given the further-deletion edge bound. -/
theorem survivorClauses_satisfied (D : Finset (Fin 57))
    (hCand : C4PolarityCanonical.Candidate D) (hDel : SurvivorDeletionBound D)
    (a : Nat → Bool) (ha : ∀ j : Fin 57, a (deletionId j) = decide (j ∈ D)) :
    cnfValue a survivorClauses = true := by
  classical
  simp only [cnfValue, List.all_eq_true, survivorClauses, List.mem_flatMap, List.mem_map,
    List.mem_reverse]
  rintro c ⟨i, _, excess, he, rfl⟩
  obtain ⟨hsub, hlen⟩ := List.mem_sublistsLen.mp he
  have hn := hsub.nodup (neighborList_nodup i)
  have hS : excess.toFinset ∈ neighborExcesses i := by
    apply Finset.mem_powersetCard.mpr
    constructor
    · rw [← neighborList_toFinset]
      intro q hq
      exact List.mem_toFinset.mpr (hsub.subset (List.mem_toFinset.mp hq))
    · rw [List.toFinset_card_of_nodup hn, hlen, ← graph.card_neighborFinset_eq_degree,
        ← neighborList_toFinset, List.toFinset_card_of_nodup (neighborList_nodup i)]
  have hperm : (excess.toFinset.sort (· ≤ ·)).Perm excess := by
    apply (List.perm_ext_iff_of_nodup (Finset.sort_nodup _ _) hn).mpr
    intro x
    simp
  have hneg (j : Fin 57) : -(deletionId j : Int) ≠ 0 := by
    have hj : deletionId j ≠ 0 := by simp [deletionId]
    exact neg_ne_zero.mpr (by exact_mod_cast hj)
  have hpos : (deletionId i : Int) ≠ 0 := by
    exact_mod_cast (show deletionId i ≠ 0 by simp [deletionId])
  have hsat := neighborDimacsClause_satisfied D (candidate_survivor_min_degree D hCand hDel)
    a ha i excess.toFinset hS
  obtain ⟨l,hl,hle⟩ := List.any_eq_true.mp hsat
  have hp := (hperm.map (fun j => -(deletionId j : Int))).cons (deletionId i : Int)
  have hl' := hp.mem_iff.mp hl
  have hnz : l ≠ 0 := by
    rcases List.mem_cons.mp hl' with h | h
    · exact h ▸ hpos
    · obtain ⟨j,_,rfl⟩ := List.mem_map.mp h
      exact hneg j
  exact List.any_eq_true.mpr ⟨l,hl', (evalLiteral_eq_literalValue a l hnz).symm ▸ hle⟩

/-- The true sentinel and the deletion variables, before any counter outputs
have been set. -/
noncomputable def deletionBase (D : Finset (Fin 57)) (v : Nat) : Bool := by
  classical
  exact if v = 1 then true else decide (∃ i ∈ D, deletionId i = v)

theorem deletionBase_true (D : Finset (Fin 57)) : deletionBase D 1 = true := by
  simp [deletionBase]

theorem deletionBase_bit (D : Finset (Fin 57)) (i : Fin 57) :
    deletionBase D (deletionId i) = decide (i ∈ D) := by
  classical
  have hne : deletionId i ≠ 1 := by unfold deletionId; omega
  simp only [deletionBase, ite_eq_right hne]
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq]
  constructor
  · rintro ⟨j,hj,heq⟩
    have hji : j = i := by
      apply Fin.ext
      unfold deletionId at heq
      omega
    exact hji ▸ hj
  · exact fun hi => ⟨i,hi,rfl⟩

private theorem deletionBits_count (D : Finset (Fin 57)) :
    (C4PolarityCanonical.deletionBits D).count true = D.card := by
  classical
  let kept := (List.finRange 57).filter fun i => decide (i ∈ D)
  have hnodup : kept.Nodup := (List.nodup_finRange 57).filter _
  have hset : kept.toFinset = D := by ext i; simp [kept]
  have hlen := List.toFinset_card_of_nodup hnodup
  rw [hset] at hlen
  rw [C4PolarityCanonical.deletionBits, List.count_eq_countP, List.countP_map]
  change (List.finRange 57).countP (fun i => decide (i ∈ D) == true) = D.card
  rw [List.countP_eq_length_filter]
  exact hlen.symm

/-- Assignment through the end of the deletion counter, before edge outputs. -/
noncomputable def deletionStage (D : Finset (Fin 57)) : Nat → Bool :=
  valuation (deletionBase D) 58 16 (C4PolarityCanonical.deletionBits D)

theorem deletionStage_bit (D : Finset (Fin 57)) (i : Fin 57) :
    deletionStage D (deletionId i) = decide (i ∈ D) := by
  unfold deletionStage
  rw [valuation_preserves]
  · exact deletionBase_bit D i
  · have := i.isLt
    unfold deletionId
    omega

theorem deletionStage_true (D : Finset (Fin 57)) : deletionStage D 1 = true := by
  unfold deletionStage
  rw [valuation_preserves _ _ _ _ _ (by decide)]
  exact deletionBase_true D

/-- The full initial block, including the sentinel, all deletion-counter
clauses, and both final deletion units. -/
theorem deletionStage_satisfies (D : Finset (Fin 57)) (hD : D.card = 15) :
    cnfValue (deletionStage D)
      ([[1]] ++ numberedCounter 58 16 (deletionVariables.map Int.ofNat) ++ [[969], [-970]]) =
      true := by
  have hbits : (deletionVariables.map Int.ofNat).map (literalValue (deletionBase D)) =
      C4PolarityCanonical.deletionBits D := by
    simp only [deletionVariables, C4PolarityCanonical.deletionBits, List.map_map,
      Function.comp_def, literalValue]
    exact List.map_congr_left (fun i _ => deletionBase_bit D i)
  have hinput : ∀ l ∈ deletionVariables.map Int.ofNat, l ≠ 0 ∧ l.natAbs ≤ 58 := by
    intro l hl
    simp only [deletionVariables, List.map_map, List.mem_map, Function.comp_apply] at hl
    obtain ⟨i,_,rfl⟩ := hl
    have hi := i.isLt
    constructor
    · change Int.ofNat _ ≠ Int.ofNat 0
      intro h
      have := Int.ofNat.inj h
      unfold deletionId at this
      omega
    · change deletionId i ≤ 58
      unfold deletionId
      omega
  have hcounter := numberedCounter_satisfied (deletionBase D) 58 16
    (deletionVariables.map Int.ofNat) (deletionBase_true D) (by decide) hinput
  rw [hbits] at hcounter
  have hunits := deletion_units_satisfied (deletionBase D) (C4PolarityCanonical.deletionBits D)
    (by simp [C4PolarityCanonical.deletionBits]) ((deletionBits_count D).trans hD)
  have hsentinel : cnfValue (deletionStage D) [[1]] = true := by
    change ((deletionStage D 1 || false) && true) = true
    simp [deletionStage_true]
  simpa only [deletionStage, cnfValue, List.all_append, Bool.and_eq_true] using
    And.intro (And.intro hsentinel hcounter) hunits

private theorem score_input_valid :
    ∀ l ∈ scoreDimacsInputs, l ≠ 0 ∧ l.natAbs ≤ 1194 := by
  intro l hl
  unfold scoreDimacsInputs at hl
  rcases List.mem_append.mp hl with h | h
  · obtain ⟨i,_,rfl⟩ := List.mem_map.mp h
    have hi := i.isLt
    have hbounds : 0 < deletionId i ∧ deletionId i ≤ 1194 := by unfold deletionId; omega
    exact ⟨by exact_mod_cast hbounds.1.ne', hbounds.2⟩
  · obtain ⟨k,rfl⟩ := List.mem_ofFn.mp h
    have hk : k.val < 224 := k.isLt.trans_le (le_of_eq orthogonalPairs_length)
    have hbounds : 0 < edgeId k.val ∧ edgeId k.val ≤ 1194 := by
      unfold edgeId deletionCounterEnd
      omega
    exact ⟨by exact_mod_cast hbounds.1.ne', hbounds.2⟩

/-- Assignment through the score counter, including the edge outputs. -/
noncomputable def scoreStage (D : Finset (Fin 57)) : Nat → Bool :=
  valuation (extendEdges (deletionStage D) orthogonalPairs) 1194 34 (scoreInputs D)

theorem scoreStage_satisfies (D : Finset (Fin 57)) (hD : C4PolarityCanonical.Candidate D) :
    cnfValue (scoreStage D) (numberedCounter 1194 34 scoreDimacsInputs ++ [[9082]]) = true := by
  let before := extendEdges (deletionStage D) orthogonalPairs
  have hbefore : before 1 = true := by
    rw [show before 1 = deletionStage D 1 from
      extendEdges_preserves_counter (deletionStage D) orthogonalPairs 1 (by decide)]
    exact deletionStage_true D
  have hmap : scoreDimacsInputs.map (literalValue before) = scoreInputs D := by
    rw [← scoreDimacsInputs_eval D (deletionStage D) (deletionStage_bit D)]
    apply List.map_congr_left
    intro l hl
    exact (evalLiteral_eq_literalValue before l (score_input_valid l hl).1).symm
  have hgates := numberedCounter_satisfied before 1194 34 scoreDimacsInputs hbefore
    (by decide) score_input_valid
  rw [hmap] at hgates
  have hunits := score_unit_satisfied before (scoreInputs D) (scoreInputs_length D)
    (by exact candidate_score_at_least_34 D hD)
  simpa only [scoreStage, before, cnfValue, List.all_append, Bool.and_eq_true] using
    And.intro hgates hunits

end Implications.C4PolarityCertifiedFormula

#print axioms Implications.C4PolarityCertifiedFormula.survivorClauses_satisfied
#print axioms Implications.C4PolarityCertifiedFormula.deletionStage_satisfies
#print axioms Implications.C4PolarityCertifiedFormula.scoreStage_satisfies
