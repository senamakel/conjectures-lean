import Robin

/-!
# Axiom allow-list for the headline theorems

`lake build RobinChecks` fails if a headline theorem picks up an axiom outside the allowed set:
`propext`, `Classical.choice`, `Quot.sound` and `native_decide` axioms
(`*._native.native_decide.ax_*`). In particular `sorryAx` fails it.
-/

open Lean Elab Command

/-- Fail unless every axiom of the constant is allowed; report the `native_decide` count. -/
elab "#assert_axioms " id:ident : command => do
  let n ← liftCoreM (realizeGlobalConstNoOverloadWithInfo id)
  let axs ← liftCoreM (Lean.collectAxioms n)
  let mut nd : Nat := 0
  for a in axs do
    if a == ``propext || a == ``Classical.choice || a == ``Quot.sound then continue
    if (a.toString.splitOn "._native.native_decide.ax_").length > 1 then
      nd := nd + 1
      continue
    throwError "{n} depends on a disallowed axiom: {a}"
  logInfo m!"{n}: {axs.size} axioms, {nd} of them native_decide; all allowed"

/--
info: 'Robin.robin_of_RH_of_verified' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Robin.robin_of_RH_of_verified

/--
info: 'Robin.lagarias_of_RH_of_verified' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Robin.Lagarias.midCheck_range._native.native_decide.ax_1_1]
-/
#guard_msgs in
#print axioms Robin.lagarias_of_RH_of_verified

#assert_axioms Robin.robin_verified_range
#assert_axioms Robin.robin_of_RH
#assert_axioms Robin.lagarias_of_RH
