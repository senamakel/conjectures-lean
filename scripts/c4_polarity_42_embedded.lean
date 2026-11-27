import Implications.C4PolarityFullAssignment
import Implications.C4PolaritySymmetryCertificate
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

end Implications.C4PolarityEmbedded

#print axioms Implications.C4PolarityEmbedded.no_candidate
