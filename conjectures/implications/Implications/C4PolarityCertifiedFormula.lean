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

end Implications.C4PolarityCertifiedFormula

#print axioms Implications.C4PolarityCertifiedFormula.survivorClauses_satisfied
