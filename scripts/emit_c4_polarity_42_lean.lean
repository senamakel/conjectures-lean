import Lean.Data.Json
import Implications.C4PolarityCertifiedFormula

open Lean Implications.C4PolarityCertifiedFormula Implications.C4PolarityLexEncoding

/-- Emit the Lean reconstruction of the DIMACS instance. Use the encoder's
ordered permutation list as input so this check compares clause generation
with exactly the same symmetry choices. -/
def main (args : List String) : IO UInt32 := do
  let [path] := args | throw (IO.userError "usage: emit_c4_polarity_42_lean.lean PERMUTATIONS.json")
  let input ← IO.FS.readFile path
  let .ok json := Json.parse input | throw (IO.userError "invalid permutation JSON")
  let .ok (permutations : List (List Nat)) := fromJson? json
    | throw (IO.userError "expected a list of permutations")
  let clauses := instanceClauses permutations
  let variableCount := orbitLexNext 9083 deletionVariables permutations - 1
  let stdout ← IO.getStdout
  stdout.putStrLn s!"p cnf {variableCount} {clauses.length}"
  for clause in clauses do
    stdout.putStrLn (String.intercalate " " (clause.map toString ++ ["0"]))
  return 0
