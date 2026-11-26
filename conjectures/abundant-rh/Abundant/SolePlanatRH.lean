import Abundant.SolePlanat
import Nicolas.Main

/-!
# Solé–Planat under RH

`solePlanat_of_nicolas` with nicolas-rh's `Nicolas.nicolas_of_RH`.
-/

namespace Abundant

/-- **Solé–Planat** (2011, Theorem 1): under RH, `Ψ(N_n)/(N_n log log N_n) > e^γ/ζ(2)` for
every `n ≥ 3`. -/
theorem solePlanat_of_RH (hRH : RiemannHypothesis) : SolePlanatStatement :=
  solePlanat_of_nicolas (Nicolas.nicolas_of_RH hRH)

end Abundant
