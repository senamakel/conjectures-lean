import Lean.Data.Json
import Implications.C4PolarityCounterAssignment
import Implications.C4PolarityEncoderInputs
import Implications.C4PolarityLexEncoding

open Lean
open C4PolarityOrderSeven
open Implications.C4PolarityCounterAssignment Implications.C4PolarityEncoderInputs
open Implications.C4PolarityEdgeEncoding Implications.C4PolarityLexEncoding

private def survivorClauses : List (List Int) :=
  (List.finRange 57).flatMap fun i =>
    let neighbors := (List.finRange 57).filter fun j => decide (i ≠ j ∧ orthogonal i j)
    (neighbors.sublistsLen (neighbors.length - 5)).reverse.map fun excess =>
      (deletionId i : Int) :: excess.map fun j => -(deletionId j : Int)

private def deletionVariables : List Nat :=
  (List.finRange 57).map deletionId

private def instanceClauses (permutations : List (List Nat)) : List (List Int) :=
  [[1]] ++ numberedCounter 58 16 (deletionVariables.map Int.ofNat) ++ [[969], [-970]] ++
    edgeFormula orthogonalPairs ++ numberedCounter 1194 34 scoreDimacsInputs ++ [[9082]] ++
    survivorClauses ++ orbitLexClauses 1 9083 deletionVariables permutations

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
