import Cramer.Main
open Lean Meta

def ours (env : Environment) (n : Name) : Option Name := do
  let idx ← env.getModuleIdxFor? n
  let m := env.header.moduleNames[idx.toNat]!
  let r := m.getRoot
  if r == `Cramer || r == `Erdos985 || r == `Vendor then some m else none

partial def closure (env : Environment) (roots : List Name) : NameSet := Id.run do
  let mut seen : NameSet := {}
  let mut stack := roots
  while !stack.isEmpty do
    match stack with
    | [] => break
    | n :: rest =>
      stack := rest
      if seen.contains n then continue
      seen := seen.insert n
      match env.find? n with
      | none => pure ()
      | some ci =>
        let mut cs := ci.type.getUsedConstants.toList
        if let some v := ci.value? (allowOpaque := true) then cs := cs ++ v.getUsedConstants.toList
        match ci with
        | .inductInfo ii => cs := cs ++ ii.ctors
        | _ => pure ()
        for c in cs do
          if !seen.contains c && (ours env c).isSome then stack := c :: stack
  return seen

run_meta do
  let env ← getEnv
  let used := closure env [`Cramer.cramer_of_RH]
  let mut out : Array String := #[]
  for (n, _) in env.constants.map₁.toList do
    if let some m := ours env n then
      if let some r ← findDeclarationRanges? n then
        let u := if used.contains n then 1 else 0
        out := out.push s!"{m}\t{n}\t{u}\t{r.range.pos.line}\t{r.range.pos.column}\t{r.range.endPos.line}\t{r.range.endPos.column}"
  IO.FS.writeFile "/home/ubuntu/work/personal/oma-wt/cramer/.oma/work/decls.tsv" (String.intercalate "\n" out.toList)
  IO.println s!"used {used.size} total {out.size}"
