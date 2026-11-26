import Mathlib

/-!
# Four exponentials ⇒ `2^t` or `3^t` is transcendental for irrational `t`

Both statements are copied word for word from formal-conjectures (commit `9097e2f`),
`FormalConjectures/Wikipedia/Exponentials.lean`:

* `Exponentials.four_exponentials_conjecture` (open), stated here as the `Prop`
  `FourExponentialsConjecture`;
* `Exponentials.two_pow_three_pow_transcendental` (open), stated here as the `Prop`
  `TwoPowThreePowTranscendental`.

The deduction is the one in the formal-conjectures docstring (and on the Wikipedia page): apply
the four exponentials conjecture to `x = (1, t)` and `y = (log 2, log 3)`. The pair `(1, t)` is
`ℚ`-linearly independent because `t` is irrational, and `(log 2, log 3)` is because
`2^a ≠ 3^b` for natural `(a, b) ≠ (0, 0)`. Of the four exponentials, `e^{log 2} = 2` and
`e^{log 3} = 3` are algebraic, so `2^t` or `3^t` is transcendental.
-/

open Complex

namespace Implications.FourExponentials

/-- **Four exponentials conjecture**, verbatim from formal-conjectures `9097e2f`,
`FormalConjectures/Wikipedia/Exponentials.lean`, `Exponentials.four_exponentials_conjecture`:
let $x_0, x_1$ and $y_0, y_1$ be $\mathbb Q$-linearly independent pairs of complex numbers,
then some $e^{x_i y_j}$ is transcendental. -/
set_option linter.unusedVariables false in
def FourExponentialsConjecture : Prop :=
  ∀ (x : Fin 2 → ℂ) (y : Fin 2 → ℂ)
    (h1 : LinearIndependent ℚ x) (h2 : LinearIndependent ℚ y),
    ∃ i j : Fin 2, Transcendental ℚ (exp (x i * y j))

/-- Verbatim from formal-conjectures `9097e2f`, `FormalConjectures/Wikipedia/Exponentials.lean`,
`Exponentials.two_pow_three_pow_transcendental`: for any irrational number $t$, at least one of
the numbers $2^t$ and $3^t$ is transcendental. -/
set_option linter.unusedVariables false in
def TwoPowThreePowTranscendental : Prop :=
  ∀ (t : ℝ) (h : Irrational t),
    Transcendental ℚ (2 ^ t : ℝ) ∨ Transcendental ℚ (3 ^ t : ℝ)

/-- `2^a = 3^b` in `ℕ` forces `a = 0` and `b = 0`. -/
lemma two_pow_eq_three_pow {a b : ℕ} (h : 2 ^ a = 3 ^ b) : a = 0 ∧ b = 0 := by
  have ha : a = 0 := by
    by_contra ha
    have h2 : 2 ∣ 3 ^ b := h ▸ dvd_pow_self 2 ha
    have := Nat.prime_two.dvd_of_dvd_pow h2
    omega
  subst ha
  exact ⟨rfl, (Nat.pow_eq_one.mp h.symm).resolve_left (by norm_num)⟩

/-- Integer relations: `m log 2 + n log 3 = 0` forces `m = n = 0`. -/
lemma int_log_two_log_three {m n : ℤ} (h : (m : ℝ) * Real.log 2 + n * Real.log 3 = 0) :
    m = 0 ∧ n = 0 := by
  have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have habs : |(m : ℝ)| * Real.log 2 = |(n : ℝ)| * Real.log 3 := by
    have e : (m : ℝ) * Real.log 2 = -((n : ℝ) * Real.log 3) := by linarith
    have := congrArg abs e
    rwa [abs_neg, abs_mul, abs_mul, abs_of_pos h2, abs_of_pos h3] at this
  rw [← Int.cast_abs, ← Int.cast_abs, ← Nat.cast_natAbs, ← Nat.cast_natAbs] at habs
  rw [← Real.log_pow, ← Real.log_pow] at habs
  have hpow : (2 : ℝ) ^ m.natAbs = 3 ^ n.natAbs :=
    Real.log_injOn_pos (Set.mem_Ioi.mpr (by positivity)) (Set.mem_Ioi.mpr (by positivity)) habs
  have hpow' : 2 ^ m.natAbs = 3 ^ n.natAbs := by exact_mod_cast hpow
  obtain ⟨hm, hn⟩ := two_pow_eq_three_pow hpow'
  exact ⟨Int.natAbs_eq_zero.mp hm, Int.natAbs_eq_zero.mp hn⟩

/-- `log 2` and `log 3` are `ℚ`-linearly independent. -/
lemma linearIndependent_log_two_log_three :
    LinearIndependent ℚ ![(Real.log 2 : ℂ), (Real.log 3 : ℂ)] := by
  rw [LinearIndependent.pair_iff]
  intro a b hab
  simp only [Rat.smul_def] at hab
  have hR : (a : ℝ) * Real.log 2 + b * Real.log 3 = 0 := by
    have : (((a : ℝ) * Real.log 2 + b * Real.log 3 : ℝ) : ℂ) = 0 := by
      push_cast; exact hab
    exact_mod_cast this
  have hZ : ((a.num * b.den : ℤ) : ℝ) * Real.log 2 + ((b.num * a.den : ℤ) : ℝ) * Real.log 3
      = 0 := by
    have ha : (a : ℝ) = a.num / a.den := by exact_mod_cast (Rat.num_div_den a).symm
    have hb : (b : ℝ) = b.num / b.den := by exact_mod_cast (Rat.num_div_den b).symm
    have hda : (a.den : ℝ) ≠ 0 := by exact_mod_cast a.den_ne_zero
    have hdb : (b.den : ℝ) ≠ 0 := by exact_mod_cast b.den_ne_zero
    rw [ha, hb] at hR
    have : ((a.num : ℝ) * b.den) * Real.log 2 + ((b.num : ℝ) * a.den) * Real.log 3
        = (a.den * b.den) * ((a.num / a.den) * Real.log 2 + (b.num / b.den) * Real.log 3) := by
      field_simp
    push_cast
    rw [this, hR, mul_zero]
  obtain ⟨hm, hn⟩ := int_log_two_log_three hZ
  refine ⟨?_, ?_⟩
  · have : a.num = 0 := by
      rcases mul_eq_zero.mp hm with h | h
      · exact h
      · exact absurd h (by exact_mod_cast b.den_ne_zero)
    exact Rat.num_eq_zero.mp this
  · have : b.num = 0 := by
      rcases mul_eq_zero.mp hn with h | h
      · exact h
      · exact absurd h (by exact_mod_cast a.den_ne_zero)
    exact Rat.num_eq_zero.mp this

/-- `1` and an irrational `t` are `ℚ`-linearly independent. -/
lemma linearIndependent_one_irrational {t : ℝ} (ht : Irrational t) :
    LinearIndependent ℚ ![(1 : ℂ), (t : ℂ)] := by
  rw [LinearIndependent.pair_iff]
  intro a b hab
  simp only [Rat.smul_def, mul_one] at hab
  have hR : (a : ℝ) + b * t = 0 := by
    have : (((a : ℝ) + b * t : ℝ) : ℂ) = 0 := by push_cast; exact hab
    exact_mod_cast this
  have hb : b = 0 := by
    by_contra hb
    have hb' : (b : ℝ) ≠ 0 := by exact_mod_cast hb
    apply ht
    refine ⟨-a / b, ?_⟩
    push_cast
    field_simp
    linarith
  subst hb
  refine ⟨?_, rfl⟩
  simpa using hR

/-- A natural number, viewed in `ℂ`, is not transcendental over `ℚ`. -/
lemma not_transcendental_natCast (k : ℕ) : ¬ Transcendental ℚ (k : ℂ) :=
  fun h => h (isAlgebraic_natCast k)

/-- For a real `r`, transcendence of `(r : ℂ)` over `ℚ` is transcendence of `r`. -/
lemma transcendental_ofReal_iff (r : ℝ) : Transcendental ℚ (r : ℂ) ↔ Transcendental ℚ r :=
  transcendental_algebraMap_iff (S := ℝ) (A := ℂ) Complex.ofReal_injective

/-- `exp (s * log b) = b ^ s` for real `s` and `b > 0`, as complex numbers. -/
lemma exp_mul_log_eq_rpow (s b : ℝ) (hb : 0 < b) :
    exp ((s : ℂ) * (Real.log b : ℂ)) = ((b ^ s : ℝ) : ℂ) := by
  rw [Real.rpow_def_of_pos hb, ← Complex.ofReal_mul, ← Complex.ofReal_exp, mul_comm]

/-- **Four exponentials ⇒ `2^t` or `3^t` is transcendental** (the formal-conjectures
statement `Exponentials.two_pow_three_pow_transcendental`, from
`Exponentials.four_exponentials_conjecture`). -/
theorem twoPowThreePowTranscendental_of_fourExponentials (h : FourExponentialsConjecture) :
    TwoPowThreePowTranscendental := by
  intro t ht
  obtain ⟨i, j, hij⟩ := h ![(1 : ℂ), (t : ℂ)] ![(Real.log 2 : ℂ), (Real.log 3 : ℂ)]
    (linearIndependent_one_irrational ht) linearIndependent_log_two_log_three
  have h2 : exp ((Real.log 2 : ℝ) : ℂ) = ((2 : ℕ) : ℂ) := by
    rw [← Complex.ofReal_exp, Real.exp_log (by norm_num)]; norm_num
  have h3 : exp ((Real.log 3 : ℝ) : ℂ) = ((3 : ℕ) : ℂ) := by
    rw [← Complex.ofReal_exp, Real.exp_log (by norm_num)]; norm_num
  fin_cases i <;> fin_cases j
  · simp only [Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero, one_mul] at hij
    rw [h2] at hij; exact absurd hij (not_transcendental_natCast 2)
  · simp only [Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero, Fin.mk_one,
      Matrix.cons_val_one, one_mul] at hij
    rw [h3] at hij; exact absurd hij (not_transcendental_natCast 3)
  · left
    simp only [Fin.mk_one, Fin.isValue, Matrix.cons_val_one, Fin.zero_eta,
      Matrix.cons_val_zero] at hij
    rw [exp_mul_log_eq_rpow t 2 (by norm_num), transcendental_ofReal_iff] at hij
    exact hij
  · right
    simp only [Fin.mk_one, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_zero] at hij
    rw [exp_mul_log_eq_rpow t 3 (by norm_num), transcendental_ofReal_iff] at hij
    exact hij

end Implications.FourExponentials
