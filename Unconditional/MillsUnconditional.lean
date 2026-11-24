import Main      -- leanprover-community/riemann-hypothesis: `riemannHypothesis`
import Mills

/-!
# Mills' constant, with RH supplied by the riemann-hypothesis repository

Not part of the default build: it needs the riemann-hypothesis project's compiled modules.
Run `scripts/check-unconditional.sh` to check it.
-/

theorem mills_constant_bounds_unconditional {A : ℝ} (hA : Mills.IsMinMills A) :
    A ∈ Set.Ioo (1.3063778838 : ℝ) 1.3063778839 :=
  Mills.mills_bounds_of_RH riemannHypothesis hA

#print axioms mills_constant_bounds_unconditional
