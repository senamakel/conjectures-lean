import Implications.C4PolarityCertifiedFormula

/-! Assemble the exact certified clause blocks under a single valuation. -/

set_option maxRecDepth 10000

namespace Implications.C4PolarityFullAssignment

open C4PolarityCertifiedFormula C4PolarityCounterAssignment C4PolarityThresholdEncoding
open C4PolarityEdgeEncoding C4PolarityEncoderInputs C4PolarityLexEncoding
open C4PolarityDimacs C4PolarityLratBridge C4PolarityCnfGates

private theorem thresholdVar_valid (base width rows row k : Nat)
    (hr : row < rows) (_hk : 0 < k) (hw : k ≤ width) :
    (thresholdVar base width row k).natAbs ≤ base + rows * width := by
  have h := Nat.mul_le_mul_right width (show row + 1 ≤ rows by omega)
  rw [Nat.succ_mul] at h
  change base + row * width + k ≤ base + rows * width
  omega

private theorem previous_bound (base width rows row k : Nat) (hb : 1 ≤ base)
    (hr : row < rows) (hk : k ≤ width) :
    (previous base width row k).natAbs ≤ base + rows * width := by
  unfold previous
  split
  · change 1 ≤ _
    omega
  · rename_i hpos
    split
    · change 1 ≤ _
      omega
    · exact thresholdVar_valid base width rows (row - 1) k (by omega) (by omega) hk

private theorem counter_bound (base width : Nat) (inputs : List Int) (hb : 1 ≤ base)
    (hinput : ∀ l ∈ inputs, l.natAbs ≤ base) :
    ∀ c ∈ numberedCounter base width inputs, ∀ l ∈ c, l.natAbs ≤ base + inputs.length * width := by
  intro c hc l hl
  simp only [numberedCounter, List.mem_flatMap] at hc
  obtain ⟨row, _, col, _, hcl⟩ := hc
  have hout := thresholdVar_valid base width inputs.length row.val (col.val + 1)
    row.isLt (by omega) col.isLt
  have ha := previous_bound base width inputs.length row.val (col.val + 1) hb row.isLt col.isLt
  have hb' := previous_bound base width inputs.length row.val col.val hb row.isLt
    (Nat.le_of_lt col.isLt)
  have hx := hinput inputs[row.val] (List.getElem_mem row.isLt)
  simp only [thresholdGateDimacs, List.mem_cons, List.not_mem_nil, or_false] at hcl
  rcases hcl with rfl | rfl | rfl | rfl <;>
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hl <;>
    rcases hl with rfl | rfl | rfl <;> (try simp only [Int.natAbs_neg]) <;> omega

private theorem deletion_bound :
    ∀ c ∈ ([[1]] ++ numberedCounter 58 16 (deletionVariables.map Int.ofNat) ++ [[969], [-970]]),
      ∀ l ∈ c, l.natAbs ≤ 970 := by
  have hinput : ∀ l ∈ deletionVariables.map Int.ofNat, l.natAbs ≤ 58 := by
    simp only [deletionVariables, List.map_map, List.mem_map, Function.comp_apply]
    rintro _ ⟨i, _, rfl⟩
    have hi := i.isLt
    change deletionId i ≤ 58
    unfold deletionId
    omega
  have hc := counter_bound 58 16 (deletionVariables.map Int.ofNat) (by decide) hinput
  have hn : 58 + (deletionVariables.map Int.ofNat).length * 16 = 970 := by
    simp [deletionVariables]
  rw [hn] at hc
  intro c hc' l hl
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hc'
  rcases hc' with (rfl | h) | rfl | rfl
  · have h := List.mem_singleton.mp hl; subst l; decide
  · exact hc c h l hl
  · have h := List.mem_singleton.mp hl; subst l; decide
  · have h := List.mem_singleton.mp hl; subst l; decide

private theorem edge_valid :
    ∀ c ∈ edgeFormula orthogonalPairs, ∀ l ∈ c, l ≠ 0 ∧ l.natAbs ≤ 1194 := by
  intro c hc l hl
  simp only [edgeFormula, List.mem_flatMap] at hc
  obtain ⟨k,_,hc⟩ := hc
  have hk : k.val < 224 := k.isLt.trans_le (le_of_eq orthogonalPairs_length)
  have he : 0 < edgeId k.val ∧ edgeId k.val ≤ 1194 := by
    unfold edgeId deletionCounterEnd
    omega
  have hd (i : Fin 57) : 0 < deletionId i ∧ deletionId i ≤ 1194 := by
    have hi := i.isLt
    unfold deletionId
    omega
  let p := orthogonalPairs[k]
  change c ∈ edgeClauses k.val p at hc
  have hx := hd p.1
  have hy := hd p.2
  simp only [edgeClauses, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;>
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hl <;>
    rcases hl with rfl | rfl | rfl <;>
    apply And.intro <;> (try simp only [Int.natAbs_neg, Int.natAbs_natCast, neg_ne_zero,
      Nat.cast_ne_zero]) <;> omega

private theorem score_bound :
    ∀ c ∈ (numberedCounter 1194 34 scoreDimacsInputs ++ [[9082]]),
      ∀ l ∈ c, l.natAbs ≤ 9082 := by
  have hlen : scoreDimacsInputs.length = 232 := by
    simp only [scoreDimacsInputs, List.length_append, List.length_map, List.length_ofFn,
      absoluteIndices_length, orthogonalPairs_length]
  have h := counter_bound 1194 34 scoreDimacsInputs (by decide)
    (fun l hl => (score_input_valid l hl).2)
  intro c hc l hl
  rcases List.mem_append.mp hc with hc | hc
  · simpa [hlen] using h c hc l hl
  · have ec := List.mem_singleton.mp hc
    subst c
    have el := List.mem_singleton.mp hl
    subst l
    decide

private theorem edgeStage_satisfies (D : Finset (Fin 57)) :
    cnfValue (extendEdges (deletionStage D) orthogonalPairs) (edgeFormula orthogonalPairs) =
      true := by
  let a := extendEdges (deletionStage D) orthogonalPairs
  have hs := edgeFormula_satisfied (deletionStage D) orthogonalPairs
  apply List.all_eq_true.mpr
  intro c hc
  obtain ⟨l,hl,hle⟩ := List.any_eq_true.mp (List.all_eq_true.mp hs c hc)
  exact List.any_eq_true.mpr ⟨l,hl,(evalLiteral_eq_literalValue a l (edge_valid c hc l hl).1).symm ▸ hle⟩

theorem scoreStage_true (D : Finset (Fin 57)) : scoreStage D 1 = true := by
  unfold scoreStage
  rw [valuation_preserves _ _ _ _ _ (by decide), extendEdges_preserves_counter _ _ _ (by decide)]
  exact deletionStage_true D

theorem scoreStage_bit (D : Finset (Fin 57)) (i : Fin 57) :
    scoreStage D (deletionId i) = decide (i ∈ D) := by
  unfold scoreStage
  rw [valuation_preserves, extendEdges_at_deletion]
  · exact deletionStage_bit D i
  · have hi := i.isLt
    unfold deletionId
    omega

/-- A graph candidate supplies one assignment to the complete reconstructed
formula whenever the supplied permutations meet the lex comparisons. -/
theorem instance_satisfied (D : Finset (Fin 57)) (hD : C4PolarityCanonical.Candidate D)
    (hDel : SurvivorDeletionBound D) (permutations : List (List Nat))
    (hp : ∀ p ∈ permutations, p.length = deletionVariables.length ∧
      (∀ i ∈ p, i < deletionVariables.length) ∧
      lexAtLeast (deletionVariables.map (scoreStage D))
        ((permutationVariables deletionVariables p).map (scoreStage D)) = true) :
    ∃ a : Nat → Bool, cnfValue a (instanceClauses permutations) = true := by
  let a := orbitLexAssignment 1 9083 deletionVariables (scoreStage D) permutations
  have hpres : ∀ n < 9083, a n = scoreStage D n :=
    orbitLexAssignment_preserves 1 9083 deletionVariables (scoreStage D) permutations
  have hedge (n : Nat) (hn : n ≤ 1194) :
      a n = extendEdges (deletionStage D) orthogonalPairs n := by
    rw [hpres n (by omega)]
    exact valuation_preserves _ _ _ _ _ hn
  have hdel (n : Nat) (hn : n ≤ 970) : a n = deletionStage D n := by
    rw [hedge n (by omega)]
    exact extendEdges_preserves_counter _ _ _ hn
  have hd : cnfValue a
      ([[1]] ++ numberedCounter 58 16 (deletionVariables.map Int.ofNat) ++ [[969], [-970]]) =
      true := by
    rw [cnfValue_congr_of_bound a (deletionStage D) _ 971
      (fun n hn => hdel n (by omega)) (fun c hc l hl => by have := deletion_bound c hc l hl; omega)]
    exact deletionStage_satisfies D hD.1
  have he : cnfValue a (edgeFormula orthogonalPairs) = true := by
    rw [cnfValue_congr_of_bound a _ _ 1195
      (fun n hn => hedge n (by omega)) (fun c hc l hl => by have := (edge_valid c hc l hl).2; omega)]
    exact edgeStage_satisfies D
  have hs : cnfValue a (numberedCounter 1194 34 scoreDimacsInputs ++ [[9082]]) = true := by
    rw [cnfValue_congr_of_bound a (scoreStage D) _ 9083 hpres
      (fun c hc l hl => by have := score_bound c hc l hl; omega)]
    exact scoreStage_satisfies D hD
  have hsurv : cnfValue a survivorClauses = true :=
    survivorClauses_satisfied D hD hDel a (fun i => by
      have hi := i.isLt
      rw [hpres _ (by unfold deletionId; omega)]
      exact scoreStage_bit D i)
  have hlex : cnfValue a (orbitLexClauses 1 9083 deletionVariables permutations) = true := by
    apply orbitLexClauses_satisfied 1 9083 deletionVariables (scoreStage D) permutations
      (by decide) (by decide) (scoreStage_true D)
    · intro n hn
      unfold deletionVariables at hn
      obtain ⟨i,_,rfl⟩ := List.mem_map.mp hn
      have hi := i.isLt
      unfold deletionId
      omega
    · exact hp
  exact ⟨a, by
    simpa only [instanceClauses, cnfValue, List.all_append, Bool.and_eq_true,
      and_assoc] using And.intro hd (And.intro he (And.intro hs (And.intro hsurv hlex)))⟩

open C4PolarityOrderSeven
open Std.Tactic.BVDecide

private theorem deletionVariables_at (i : Fin 57) :
    deletionVariables[i.val]! = deletionId i := by
  have hi : i.val < deletionVariables.length := by simpa [deletionVariables] using i.isLt
  rw [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem hi]
  simp [deletionVariables, List.getElem_finRange, Fin.eta]

/-- A checked trace excludes a qualifying deletion if its symmetry rows are
graph automorphisms and the further-deletion edge bound holds. -/
theorem no_candidate_of_checked_trace
    (permutations : List (List Nat)) (proof : Array LRAT.IntAction)
    (hperms : ∀ p ∈ permutations, ∃ e : graph ≃g graph,
      p = (List.finRange 57).map (fun i => (e i).val))
    (hDel : ∀ D, C4PolarityCanonical.Candidate D → SurvivorDeletionBound D)
    (hvalid : ∀ c ∈ instanceClauses permutations, ∀ l ∈ c, l ≠ 0)
    (hcheck : LRAT.check proof (toCnf ((instanceClauses permutations).map List.toArray).toArray) = true) :
    ¬ ∃ D, C4PolarityCanonical.Candidate D := by
  intro h
  obtain ⟨D,hD,_,hmax⟩ := C4PolarityCanonical.exists_canonical_deletion_score h
  have hp : ∀ p ∈ permutations, p.length = deletionVariables.length ∧
      (∀ i ∈ p, i < deletionVariables.length) ∧
      lexAtLeast (deletionVariables.map (scoreStage D))
        ((permutationVariables deletionVariables p).map (scoreStage D)) = true := by
    intro p hp
    obtain ⟨e,rfl⟩ := hperms p hp
    refine ⟨by simp [deletionVariables], ?_, ?_⟩
    · intro n hn
      obtain ⟨i,_,rfl⟩ := List.mem_map.mp hn
      simpa [deletionVariables] using (e i).isLt
    · have hl : deletionVariables.map (scoreStage D) =
          C4PolarityCanonical.deletionBits D := by
        simp only [deletionVariables, C4PolarityCanonical.deletionBits, List.map_map,
          Function.comp_def, scoreStage_bit]
      have hr : (permutationVariables deletionVariables
            ((List.finRange 57).map (fun i => (e i).val))).map (scoreStage D) =
          (List.finRange 57).map (fun i => decide (e i ∈ D)) := by
        simp only [permutationVariables, List.map_map, Function.comp_def,
          deletionVariables_at, scoreStage_bit]
      rw [hl, hr]
      exact lexAtLeast_eq_true_of_le _ _ (by simp [C4PolarityCanonical.deletionBits]) (hmax e)
  obtain ⟨a, ha⟩ := instance_satisfied D hD (hDel D hD) permutations hp
  have hfalse := no_encoder_assignment_of_check proof (instanceClauses permutations)
    hvalid hcheck a
  rw [ha] at hfalse
  contradiction

/-- Validate the signed literal convention and replay the trace against the
reconstructed formula itself. -/
def replayAccepts (permutations : List (List Nat)) (proof : Array LRAT.IntAction) : Bool :=
  let clauses := instanceClauses permutations
  clauses.all (fun c => c.all (· != 0)) &&
    LRAT.check proof (toCnf (clauses.map List.toArray).toArray)

/-- A successful replay checks both of the certificate premises together. -/
theorem no_candidate_of_replay
    (permutations : List (List Nat)) (proof : Array LRAT.IntAction)
    (hperms : ∀ p ∈ permutations, ∃ e : graph ≃g graph,
      p = (List.finRange 57).map (fun i => (e i).val))
    (hDel : ∀ D, C4PolarityCanonical.Candidate D → SurvivorDeletionBound D)
    (hcheck : replayAccepts permutations proof = true) :
    ¬ ∃ D, C4PolarityCanonical.Candidate D := by
  unfold replayAccepts at hcheck
  obtain ⟨hvalid, hlrat⟩ := Bool.and_eq_true_iff.mp hcheck
  refine no_candidate_of_checked_trace permutations proof hperms hDel ?_ hlrat
  intro c hc l hl
  exact bne_iff_ne.mp (List.all_eq_true.mp (List.all_eq_true.mp hvalid c hc) l hl)

end Implications.C4PolarityFullAssignment

#print axioms Implications.C4PolarityFullAssignment.instance_satisfied
#print axioms Implications.C4PolarityFullAssignment.no_candidate_of_checked_trace
#print axioms Implications.C4PolarityFullAssignment.no_candidate_of_replay
