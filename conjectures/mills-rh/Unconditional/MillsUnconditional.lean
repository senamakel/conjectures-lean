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

/-- Caldwell–Cheng's Lemma 5, unconditionally: a prime between `x³` and `(x+1)³` for every real
`x ≥ 2^{1/3} − 1`. -/
theorem prime_between_cubes_unconditional (x : ℝ) (hx : (2 : ℝ) ^ ((1 : ℝ) / 3) - 1 ≤ x) :
    ∃ p : ℕ, p.Prime ∧ x ^ 3 < p ∧ (p : ℝ) ≤ (x + 1) ^ 3 :=
  Mills.caldwellChengLemma5_of_RH riemannHypothesis x hx

/-- The strict form: a prime in `(x³, (x+1)³)` for every real `x > 2^{1/3} − 1`. -/
theorem prime_strictly_between_cubes_unconditional (x : ℝ)
    (hx : (2 : ℝ) ^ ((1 : ℝ) / 3) - 1 < x) :
    ∃ p : ℕ, p.Prime ∧ x ^ 3 < p ∧ (p : ℝ) < (x + 1) ^ 3 :=
  Mills.primeStrictlyBetweenCubes_of_RH riemannHypothesis x hx

/-- Mills' constant to 30 decimals (`Mills.MillsDigits 30`), unconditionally. -/
theorem mills_digits30_unconditional {A : ℝ} (hA : Mills.IsMinMills A) :
    ((1306377883863080690468614492602 : ℕ) : ℝ) / 10 ^ 30 ≤ A ∧
      A < (((1306377883863080690468614492602 : ℕ) : ℝ) + 1) / 10 ^ 30 :=
  Mills.millsDigits30_of_RH riemannHypothesis hA

/-- Mills' constant to 87 decimals (`Mills.MillsDigits 87`), unconditionally. -/
theorem mills_digits87_unconditional {A : ℝ} (hA : Mills.IsMinMills A) :
    ((1306377883863080690468614492602605712916784585156713644368053759966434053766826598821501 : ℕ) : ℝ) / 10 ^ 87 ≤ A ∧
      A < (((1306377883863080690468614492602605712916784585156713644368053759966434053766826598821501 : ℕ) : ℝ) + 1) / 10 ^ 87 :=
  Mills.millsDigits87_of_RH riemannHypothesis hA

#print axioms mills_constant_bounds_unconditional
#print axioms prime_between_cubes_unconditional
#print axioms prime_strictly_between_cubes_unconditional
#print axioms mills_digits30_unconditional
#print axioms mills_digits87_unconditional
