import Abundant

/-!
# Axiom allow-list for the headline theorems

`lake build AbundantChecks` fails if a headline theorem picks up an axiom outside the allowed set
(`propext`, `Classical.choice`, `Quot.sound` and the documented `native_decide`s of
`Abundant.Check.check_ok` and `Nicolas.Check.loop_ok`), in particular `sorryAx`.
-/

/--
info: 'Abundant.solePlanat_of_nicolas' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Abundant.solePlanat_of_nicolas

/--
info: 'Abundant.solePlanat_of_RH' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Nicolas.Check.loop_ok._native.native_decide.ax_1_1]
-/
#guard_msgs in
#print axioms Abundant.solePlanat_of_RH

/--
info: 'Abundant.extremelyAbundantInfinite_of_robin_of_nicolas' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Abundant.extremelyAbundantInfinite_of_robin_of_nicolas

/--
info: 'Abundant.extremelyAbundantInfinite_of_RH' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Nicolas.Check.loop_ok._native.native_decide.ax_1_1]
-/
#guard_msgs in
#print axioms Abundant.extremelyAbundantInfinite_of_RH

/--
info: 'Abundant.fourOnlyExtraordinary_of_robin_of_nicolas' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Abundant.Check.check_ok._native.native_decide.ax_1_1]
-/
#guard_msgs in
#print axioms Abundant.fourOnlyExtraordinary_of_robin_of_nicolas

/--
info: 'Abundant.fourOnlyExtraordinary_of_RH' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Abundant.Check.check_ok._native.native_decide.ax_1_1,
 Nicolas.Check.loop_ok._native.native_decide.ax_1_1]
-/
#guard_msgs in
#print axioms Abundant.fourOnlyExtraordinary_of_RH
