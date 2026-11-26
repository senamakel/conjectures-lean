import SunPi

/-!
# Axiom allow-list for the headline theorems

`lake build SunPiChecks` fails if a headline theorem picks up an axiom outside the allowed set
(`propext`, `Classical.choice`, `Quot.sound` and the one documented `native_decide`,
`SunPi.checkB_ok`), in particular `sorryAx`.
-/

/-- info: 'SunPi.sun_2_7_i' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SunPi.sun_2_7_i

/-- info: 'SunPi.oeis_A238165_ii' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SunPi.oeis_A238165_ii

/-- info: 'SunPi.sun_2_7_i_nat' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SunPi.sun_2_7_i_nat

/--
info: 'SunPi.sun_2_14_ii' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 SunPi.checkB_ok._native.native_decide.ax_1_1]
-/
#guard_msgs in
#print axioms SunPi.sun_2_14_ii

/--
info: 'SunPi.oeis_A038107_i' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 SunPi.checkB_ok._native.native_decide.ax_1_1]
-/
#guard_msgs in
#print axioms SunPi.oeis_A038107_i

/--
info: 'SunPi.sun_2_14_ii_nat' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 SunPi.checkB_ok._native.native_decide.ax_1_1]
-/
#guard_msgs in
#print axioms SunPi.sun_2_14_ii_nat

/-- info: 'SunPi.Check.checkA_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SunPi.Check.checkA_sound

/-- info: 'SunPi.Check.checkB_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SunPi.Check.checkB_sound
