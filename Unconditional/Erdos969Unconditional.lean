import Main      -- leanprover-community/riemann-hypothesis: `riemannHypothesis`
import Erdos969

/-!
# Axer's bounds for squarefree and `k`-free numbers, with RH supplied by the riemann-hypothesis repository

Not part of the default build: it needs the riemann-hypothesis project's compiled modules.
Run `scripts/check-unconditional.sh` to check it.
-/

theorem axer_unconditional : Erdos969.AxerBound :=
  Erdos969.axer_of_RH riemannHypothesis

#print axioms axer_unconditional

/-- Axer's bound for `k`-free numbers, every `k ≥ 2`. -/
theorem axerKFree_unconditional {k : ℕ} (hk : 2 ≤ k) : Erdos969.AxerKFreeBound k :=
  Erdos969.KFree.axerKFree_of_RH riemannHypothesis hk

#print axioms axerKFree_unconditional
