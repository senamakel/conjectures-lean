import Nicolas

/-!
# Axiom allow-list for the headline theorem

`lake build NicolasChecks` fails if `Nicolas.nicolas_of_RH` picks up an axiom outside the allowed
set (`propext`, `Classical.choice`, `Quot.sound` and the documented `native_decide` of
`Nicolas.Check.loop_ok`), in particular `sorryAx`.
-/

/--
info: 'Nicolas.nicolas_of_RH' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Nicolas.Check.loop_ok._native.native_decide.ax_1_1]
-/
#guard_msgs in
#print axioms Nicolas.nicolas_of_RH
