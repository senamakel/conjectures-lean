import Mathlib.Tactic.Sat.FromLRAT
import Std.Tactic.BVDecide.LRAT.Checker
import Std.Tactic.BVDecide.LRAT.Parser

open Std.Sat Std.Tactic.BVDecide

/-- Replay a DIMACS and LRAT pair with Lean's sound LRAT checker. -/
def main (args : List String) : IO UInt32 := do
  let [cnfPath, proofPath] := args
    | throw (IO.userError "usage: lean --run check_dimacs_lrat.lean FORMULA.cnf PROOF.lrat")
  let input ← IO.FS.readFile cnfPath
  let .ok (variables, clauses) := Mathlib.Tactic.Sat.Parser.parseDimacs.run input
    | throw (IO.userError "invalid DIMACS input")
  unless clauses.all (·.all fun literal => literal != 0 && literal.natAbs ≤ variables) do
    throw (IO.userError "invalid DIMACS variable")
  let formula : CNF Nat := ⟨clauses.map fun clause =>
    CNF.Clause.ofLiterals (clause.toList.map fun literal =>
      (literal.natAbs - 1, literal > 0))⟩
  let proof ← LRAT.loadLRATProof proofPath
  if LRAT.check proof formula then
    IO.println s!"LRAT verified ({variables} variables, {clauses.size} clauses, {proof.size} actions)"
    return 0
  else
    IO.eprintln "LRAT check failed"
    return 1
