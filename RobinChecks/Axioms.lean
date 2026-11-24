import Robin

/-!
# Axiom allow-list for the headline theorems

`lake build RobinChecks` fails if a headline theorem picks up an axiom outside the allowed set
(`propext`, `Classical.choice`, `Quot.sound` and the documented `native_decide` of
`Robin.Lagarias.midCheck_range`), in particular `sorryAx`.
-/

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
