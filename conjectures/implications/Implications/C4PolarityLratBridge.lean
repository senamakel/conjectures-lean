import Implications.C4PolarityDimacs
import Implications.C4PolarityThresholdEncoding

/-!
Relate the encoder's list-valued clause semantics to the array of signed
literals passed to the sound LRAT checker.
-/

namespace Implications.C4PolarityLratBridge

open C4PolarityDimacs C4PolarityThresholdEncoding
open Std.Tactic.BVDecide

theorem evalLiteral_eq_literalValue (a : Nat → Bool) (l : Int) (hl : l ≠ 0) :
    evalLiteral a l = literalValue a l := by
  cases l with
  | ofNat n =>
    have hn : 0 < n := by
      apply Nat.pos_of_ne_zero
      intro h
      subst n
      exact hl rfl
    simp [evalLiteral, literalValue, hn]
  | negSucc n =>
    simp [evalLiteral, literalValue, Int.natAbs]

theorem no_encoder_assignment_of_check
    (proof : Array LRAT.IntAction) (cs : List (List Int))
    (hvalid : ∀ c ∈ cs, ∀ l ∈ c, l ≠ 0)
    (hcheck : LRAT.check proof (toCnf (cs.map List.toArray).toArray) = true)
    (a : Nat → Bool) : cnfValue a cs = false := by
  have hvalidArray : ∀ c ∈ (cs.map List.toArray).toArray, ∀ l ∈ c, l ≠ 0 := by
    intro c hc l hl
    simp only [List.mem_toArray, List.mem_map] at hc
    obtain ⟨c,hc,rfl⟩ := hc
    exact hvalid c hc l (by simpa using hl)
  have hcheck' := no_assignment_of_check proof (cs.map List.toArray).toArray hvalidArray hcheck a
  have harray : ((cs.map List.toArray).toArray).all
      (fun c => c.any (evalLiteral a)) = cs.all (fun c => c.any (evalLiteral a)) := by
    simp only [← Array.all_toList, List.all_map, Function.comp_def,
      ← Array.any_toList]
  rw [harray] at hcheck'
  unfold cnfValue
  have heq : cs.all (clauseValue a) = cs.all (fun c => c.any (evalLiteral a)) := by
    apply Bool.eq_iff_iff.mpr
    simp only [List.all_eq_true]
    have hclause (c : List Int) (hc : c ∈ cs) :
        clauseValue a c = c.any (evalLiteral a) := by
      unfold clauseValue
      apply Bool.eq_iff_iff.mpr
      simp only [List.any_eq_true]
      exact ⟨fun ⟨l,hl,h⟩ => ⟨l,hl,(evalLiteral_eq_literalValue a l (hvalid c hc l hl)).symm ▸ h⟩,
        fun ⟨l,hl,h⟩ => ⟨l,hl,evalLiteral_eq_literalValue a l (hvalid c hc l hl) ▸ h⟩⟩
    exact ⟨fun h c hc => hclause c hc ▸ h c hc, fun h c hc => (hclause c hc).symm ▸ h c hc⟩
  exact heq.trans hcheck'

end Implications.C4PolarityLratBridge

#print axioms Implications.C4PolarityLratBridge.no_encoder_assignment_of_check
