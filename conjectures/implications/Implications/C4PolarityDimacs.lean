import Std.Tactic.BVDecide.LRAT.Checker

/-!
The signed, one-based literals emitted by the polarity encoder have the same
semantics as the zero-based literals supplied to Lean's LRAT checker.
-/

namespace Implications.C4PolarityDimacs

open Std.Sat Std.Tactic.BVDecide

/-- Evaluate a signed DIMACS literal using a one-based assignment. -/
def evalLiteral (a : Nat → Bool) (literal : Int) : Bool :=
  a literal.natAbs == decide (0 < literal)

/-- Use the same literal numbering and clause construction as the LRAT replay. -/
def toCnf (clauses : Array (Array Int)) : CNF Nat :=
  ⟨clauses.map fun clause => CNF.Clause.ofLiterals (clause.toList.map fun literal =>
    (literal.natAbs - 1, literal > 0))⟩

theorem eval_toCnf (a : Nat → Bool) (clauses : Array (Array Int))
    (hvalid : ∀ clause ∈ clauses, ∀ literal ∈ clause, literal ≠ 0) :
    (toCnf clauses).eval (fun i => a (i + 1)) =
      clauses.all (fun clause => clause.any (evalLiteral a)) := by
  simp only [toCnf, CNF.eval, Array.all_map]
  apply Bool.eq_iff_iff.mpr
  simp only [Array.all_eq_true]
  have hclause (clause : Array Int) (hc : clause ∈ clauses) :
      (CNF.Clause.ofLiterals (clause.toList.map fun literal =>
        (literal.natAbs - 1, literal > 0))).eval (fun i => a (i + 1)) =
        clause.any (evalLiteral a) := by
    simp only [CNF.Clause.eval, CNF.Clause.literals_ofLiterals, List.any_map,
      Array.any_toList, Function.comp_def]
    apply Bool.eq_iff_iff.mpr
    simp only [Array.any_eq_true]
    have hlit (literal : Int) (hl : literal ∈ clause) :
        (a (literal.natAbs - 1 + 1) == decide (0 < literal)) =
          evalLiteral a literal := by
      have hn : 0 < literal.natAbs :=
        Nat.pos_of_ne_zero (fun h => hvalid clause hc literal hl (Int.natAbs_eq_zero.mp h))
      simp [evalLiteral, Nat.sub_add_cancel hn]
    exact ⟨fun ⟨literal, hl, he⟩ => ⟨literal, hl, hlit clause[literal] (Array.getElem_mem hl) ▸ he⟩,
      fun ⟨literal, hl, he⟩ => ⟨literal, hl, (hlit clause[literal] (Array.getElem_mem hl)).symm ▸ he⟩⟩
  constructor
  · intro h c hc
    simpa only [Function.comp_apply, hclause clauses[c] (Array.getElem_mem hc)] using h c hc
  · intro h c hc
    simpa only [Function.comp_apply, hclause clauses[c] (Array.getElem_mem hc)] using h c hc

theorem no_assignment_of_check (proof : Array LRAT.IntAction) (clauses : Array (Array Int))
    (hvalid : ∀ clause ∈ clauses, ∀ literal ∈ clause, literal ≠ 0)
    (hcheck : LRAT.check proof (toCnf clauses) = true) (a : Nat → Bool) :
    clauses.all (fun clause => clause.any (evalLiteral a)) = false := by
  have h := LRAT.check_sound proof (toCnf clauses) hcheck (fun i => a (i + 1))
  rw [eval_toCnf a clauses hvalid] at h
  simpa using h

end Implications.C4PolarityDimacs

#print axioms Implications.C4PolarityDimacs.no_assignment_of_check
