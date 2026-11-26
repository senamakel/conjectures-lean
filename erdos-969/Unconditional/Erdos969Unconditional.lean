import Main      -- leanprover-community/riemann-hypothesis: `riemannHypothesis`
import Erdos969

/-!
# Axer's and Montgomery–Vaughan's bounds, with RH supplied by the riemann-hypothesis repository

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

/-- Montgomery–Vaughan's bound for `k`-free numbers, every `k ≥ 2`:
`E_k(x) = O(x^{1/(k+1)+ε})`. -/
theorem montgomeryVaughan_unconditional {k : ℕ} (hk : 2 ≤ k) : Erdos969.MontgomeryVaughanBound k :=
  Erdos969.MV.montgomeryVaughan_of_RH riemannHypothesis hk

#print axioms montgomeryVaughan_unconditional

/-- The squarefree case: `E(x) = O(x^{1/3+ε})`. -/
theorem squarefreeError_mv_unconditional :
    ∀ ε : ℝ, 0 < ε → (fun x : ℕ => |Erdos969.squarefreeCountingError x|) =O[Filter.atTop]
      fun x : ℕ => (x : ℝ) ^ (1 / 3 + ε) :=
  Erdos969.MV.squarefreeError_mv_of_RH riemannHypothesis

#print axioms squarefreeError_mv_unconditional
