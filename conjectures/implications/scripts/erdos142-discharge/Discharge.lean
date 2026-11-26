/-
Discharge of the tier-H hypothesis of `Implications.Erdos142.FromQuantitativeDensity`, meant to
be compiled inside openai/math (`lean/`, commit adc7f1241b42e322a6451854ab7e4b4c146bf78a,
Lean v4.34.1, Mathlib d13f23b7) with `Implications/Erdos142/{Statement,FromQuantitativeDensity}.lean`
copied next to it. NOT part of the Implications library, and NOT typechecked (see README.md).
-/
import OAI.Combinatorics.Progressions.Results.Conclusions
import Implications.Erdos142.FromQuantitativeDensity

/-- Our verbatim copy `Erdos142.OAI.QuantitativeDensityTheorem` is definitionally openai/math's
`OAI.Erdos3.QuantitativeDensityTheorem` (same bodies, only the namespace differs). -/
theorem Erdos142.OAI.quantitativeDensityTheorem : Erdos142.OAI.QuantitativeDensityTheorem :=
  OAI.Erdos3.manuscriptQuantitativeDensityTheorem

/-- formal-conjectures `erdos_142.variants.lower`. -/
theorem erdos_142_variants_lower : Erdos142.VariantsLower :=
  Erdos142.variantsLower_of_quantitativeDensity Erdos142.OAI.quantitativeDensityTheorem

/-- Erdős #140 for every `k ≥ 3` (our statement). -/
theorem erdos_140_allK : Erdos140.AllK :=
  Erdos140.allK_of_quantitativeDensity Erdos142.OAI.quantitativeDensityTheorem

#print axioms erdos_142_variants_lower
#print axioms erdos_140_allK
