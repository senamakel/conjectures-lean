import Implications.C4PolarityFullAssignment
import Implications.C4PolaritySymmetryCertificate
import Implications.C4PolaritySurvivorBound
import Std.Tactic.BVDecide.LRAT.Parser

namespace Implications.C4PolarityEmbedded

open Std.Tactic.BVDecide
open C4PolarityFullAssignment C4PolaritySymmetryCertificate C4PolarityEncoderInputs

/-- Each input byte was stored as its corresponding Unicode code point. -/
def traceBytes : ByteArray :=
  (include_str "trace.utf8").foldl (fun bytes c => bytes.push c.toNat.toUInt8) ByteArray.empty

def checked : Bool :=
  match LRAT.parseLRATProof traceBytes with
  | .ok actions => replayAccepts symmetryRows actions
  | .error _ => false

theorem trace_accepted : checked = true := by native_decide

/-- The concrete polarity graph admits no candidate deletion, given the
132-edge bound on the induced 41-vertex graphs. -/
theorem no_candidate
    (hDel : ∀ D, C4PolarityCanonical.Candidate D → SurvivorDeletionBound D) :
    ¬ ∃ D, C4PolarityCanonical.Candidate D := by
  have h := trace_accepted
  unfold checked at h
  cases hparse : LRAT.parseLRATProof traceBytes with
  | error _ => simp [hparse] at h
  | ok actions =>
    exact no_candidate_of_replay symmetryRows actions hperms hDel (by simpa [hparse] using h)

/-- Exclude candidate deletions from the published general 41-vertex bound. -/
theorem no_candidate_of_ex41C4Bound
    (hEx41 : C4PolaritySurvivorBound.Ex41C4Bound) :
    ¬ ∃ D, C4PolarityCanonical.Candidate D :=
  no_candidate (C4PolaritySurvivorBound.survivorDeletionBound_of_ex41C4Bound hEx41)

/-- Every induced 42-vertex subgraph of the order-seven polarity graph has
at most 137 edges, given the general 41-vertex bound. -/
theorem induced_edge_count_le_137
    (hEx41 : C4PolaritySurvivorBound.Ex41C4Bound)
    (S : Finset (Fin 57)) (hS : S.card = 42) :
    C4PolarityDeletion.inducedEdgeCount C4PolarityOrderSeven.graph S ≤ 137 := by
  by_contra! h
  apply no_candidate_of_ex41C4Bound hEx41
  refine ⟨Sᶜ, ?_, ?_⟩
  · simp [Finset.card_compl, hS]
  · have h138 : 138 ≤ C4PolarityDeletion.inducedEdgeCount C4PolarityOrderSeven.graph S := by
      omega
    simpa [← Finset.compl_eq_univ_sdiff] using h138

end Implications.C4PolarityEmbedded

#print axioms Implications.C4PolarityEmbedded.no_candidate
#print axioms Implications.C4PolarityEmbedded.induced_edge_count_le_137
