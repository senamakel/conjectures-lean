import Polya

/-!
# Axiom allow-list for the headline theorems

`lake build PolyaChecks` fails if a headline theorem picks up an axiom outside the allowed set
(`propext`, `Classical.choice`, `Quot.sound` and its documented `native_decide`), in particular
`sorryAx`.
-/

/--
info: 'Polya.polya_conjecture_false' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Polya.Check.liouville_906150257_check._native.native_decide.ax_1_1]
-/
#guard_msgs in
#print axioms Polya.polya_conjecture_false

/--
info: 'Polya.liouvilleSum_906150257' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Polya.Check.liouville_906150257_check._native.native_decide.ax_1_1]
-/
#guard_msgs in
#print axioms Polya.liouvilleSum_906150257

/--
info: 'Polya.vonSterneck_conjecture_false' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Polya.Check.mertens_7725038629_check._native.native_decide.ax_1_1]
-/
#guard_msgs in
#print axioms Polya.vonSterneck_conjecture_false

/--
info: 'Polya.vonSterneck_conjecture_int_false' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Polya.Check.mertens_7725038629_check._native.native_decide.ax_1_1]
-/
#guard_msgs in
#print axioms Polya.vonSterneck_conjecture_int_false

/--
info: 'Polya.mertens_7725038629' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Polya.Check.mertens_7725038629_check._native.native_decide.ax_1_1]
-/
#guard_msgs in
#print axioms Polya.mertens_7725038629

/-- info: 'Polya.Check.runMertens_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Polya.Check.runMertens_sound

/-- info: 'Polya.Check.runLiouville_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Polya.Check.runLiouville_sound
