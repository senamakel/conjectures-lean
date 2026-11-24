import Density.Main

/-!
# Axiom allow-list

The build fails if any headline theorem picks up an axiom beyond the standard three
(`sorryAx` included).
-/

/-- info: 'DensityHypothesis.densityHypothesis_of_RH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms DensityHypothesis.densityHypothesis_of_RH

/-- info: 'Density.zeroCountOn_le_of_jensen' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Density.zeroCountOn_le_of_jensen

/-- info: 'Density.zeroCountOn_riemannZeta_eq_xiZeta' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Density.zeroCountOn_riemannZeta_eq_xiZeta

/-- info: 'Density.zeroCountOn_xiZeta_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Density.zeroCountOn_xiZeta_le

/-- info: 'Density.zeroCountOn_riemannZeta_le_of_subset_strip' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Density.zeroCountOn_riemannZeta_le_of_subset_strip

/-- info: 'Density.zeroCountOn_riemannZeta_le_of_subset_box' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Density.zeroCountOn_riemannZeta_le_of_subset_box
