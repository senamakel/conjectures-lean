import Mathlib

/-!
# The Lander–Parkin–Selfridge conjecture implies Erdős 324 for `x ^ 5`

Statements, copied word for word from formal-conjectures at commit `9097e2f` as `def … : Prop`:

* `LanderParkinSelfridge.lander_parkin_selfridge` and
  `LanderParkinSelfridge.lander_parkin_selfridge.variants.five_three`
  (`FormalConjectures/Wikipedia/LanderParkinAndSelfridgeConjecture.lean`, research open);
* `Erdos324.erdos_324.variants.quintic` and `Erdos324.erdos_324`
  (`FormalConjectures/ErdosProblems/324.lean`, research open).

`erdos_324_quintic_of_lps`: if `a ^ 5 + b ^ 5 = c ^ 5 + d ^ 5` with `a < b`, `c < d` and
`(a, b) ≠ (c, d)`, the four numbers are pairwise distinct (a shared value cancels and forces the
pairs to agree). If none is `0`, the conjecture with `k = 5`, `n = m = 2` would give `5 ≤ 4`; if
`a = 0` (or `c = 0`), the other three are positive and `n = 1`, `m = 2` give `5 ≤ 3`. Then
`erdos_324_of_lps` takes `f = X ^ 5`. This is the folklore remark that LPS forbids nontrivial
solutions of `a⁵ + b⁵ = c⁵ + d⁵`.
-/

open scoped Polynomial

namespace Implications.Misc.LPS324

/-- Source: `FormalConjectures/Wikipedia/LanderParkinAndSelfridgeConjecture.lean`,
`LanderParkinSelfridge.lander_parkin_selfridge`, formal-conjectures `9097e2f` (research open);
the statement of the theorem, verbatim.

The Lander–Parkin–Selfridge conjecture: if the sum of $n$ positive integer $k$-th powers
equals the sum of $m$ positive integer $k$-th powers, with all values on the left distinct from
all values on the right, then $n + m \geq k$. -/
def LanderParkinSelfridgeConjecture : Prop :=
    ∀ (k n m : ℕ) (x : Fin n → ℕ) (y : Fin m → ℕ),
      0 < n → 0 < m →
      (∀ i, 0 < x i) → (∀ j, 0 < y j) →
      (∀ i j, x i ≠ y j) →
      ∑ i, x i ^ k = ∑ j, y j ^ k →
      k ≤ n + m

/-- Source: `FormalConjectures/Wikipedia/LanderParkinAndSelfridgeConjecture.lean`,
`LanderParkinSelfridge.lander_parkin_selfridge.variants.five_three`, formal-conjectures
`9097e2f` (research open); the statement, verbatim. -/
def LPSFiveThree : Prop :=
    ∀ x₁ x₂ x₃ y : ℕ,
      0 < x₁ → 0 < x₂ → 0 < x₃ → 0 < y →
      x₁ ^ 5 + x₂ ^ 5 + x₃ ^ 5 ≠ y ^ 5

/-- Source: `FormalConjectures/ErdosProblems/324.lean`, `Erdos324.erdos_324.variants.quintic`,
formal-conjectures `9097e2f` (research open); the statement, verbatim.

Probably $f(x) = x^5$ has the property that the sums $f(a)+f(b)$ with
$a < b$ nonnegative integers are distinct. -/
def Erdos324Quintic : Prop :=
  {(a, b) : ℕ × ℕ | a < b}.InjOn fun (a, b) => a ^ 5 + b ^ 5

/-- Source: `FormalConjectures/ErdosProblems/324.lean`, `Erdos324.erdos_324`,
formal-conjectures `9097e2f` (research open, `question`); the proposition, verbatim.

Does there exist a polynomial $f(x)\in\mathbb{Z}[x]$ such that all the sums $f(a)+f(b)$ with
$a < b$ nonnegative integers are distinct? -/
def Erdos324 : Prop :=
    ∃ f : ℤ[X], {(a, b) : ℕ × ℕ | a < b}.InjOn fun (a, b) => f.eval (a : ℤ) + f.eval (b : ℤ)

theorem pow5_inj {a b : ℕ} (h : a ^ 5 = b ^ 5) : a = b :=
  Nat.pow_left_injective (by norm_num : (5 : ℕ) ≠ 0) h

/-- **The Lander–Parkin–Selfridge conjecture implies `erdos_324.variants.quintic`.** -/
theorem erdos_324_quintic_of_lps (h : LanderParkinSelfridgeConjecture) : Erdos324Quintic := by
  rintro ⟨a, b⟩ hab ⟨c, d⟩ hcd hE
  simp only [Set.mem_ofPred_eq] at hab hcd
  simp only at hE
  by_contra hne
  have hne' : ¬ (a = c ∧ b = d) := fun ⟨h1, h2⟩ => hne (by rw [h1, h2])
  -- the four values are pairwise distinct
  have hac : a ≠ c := by
    rintro rfl; exact hne' ⟨rfl, pow5_inj (by omega)⟩
  have had : a ≠ d := by
    rintro rfl
    have := pow5_inj (show b ^ 5 = c ^ 5 by omega); omega
  have hbc : b ≠ c := by
    rintro rfl
    have := pow5_inj (show a ^ 5 = d ^ 5 by omega); omega
  have hbd : b ≠ d := by
    rintro rfl; exact hne' ⟨pow5_inj (by omega), rfl⟩
  rcases Nat.eq_zero_or_pos a with ha0 | ha0
  · subst ha0
    have hc : 0 < c := Nat.pos_of_ne_zero (Ne.symm hac)
    have := h 5 1 2 ![b] ![c, d] one_pos two_pos (by simp; omega) (by simp [Fin.forall_fin_two]; omega)
      (by simp [Fin.forall_fin_two]; omega) (by simp [Fin.sum_univ_two]; simpa using hE)
    omega
  · rcases Nat.eq_zero_or_pos c with hc0 | hc0
    · subst hc0
      have := h 5 2 1 ![a, b] ![d] two_pos one_pos (by simp [Fin.forall_fin_two]; omega)
        (by simp; omega) (by simp [Fin.forall_fin_two]; omega)
        (by simp [Fin.sum_univ_two]; simpa using hE)
      omega
    · have := h 5 2 2 ![a, b] ![c, d] two_pos two_pos (by simp [Fin.forall_fin_two]; omega)
        (by simp [Fin.forall_fin_two]; omega) (by simp [Fin.forall_fin_two]; omega)
        (by simp [Fin.sum_univ_two]; exact hE)
      omega

/-- **The Lander–Parkin–Selfridge conjecture implies Erdős 324** (`f = X ^ 5`). -/
theorem erdos_324_of_lps (h : LanderParkinSelfridgeConjecture) : Erdos324 := by
  refine ⟨Polynomial.X ^ 5, ?_⟩
  rintro ⟨a, b⟩ hab ⟨c, d⟩ hcd hE
  simp only [Polynomial.eval_pow, Polynomial.eval_X] at hE
  exact erdos_324_quintic_of_lps h hab hcd (by simp only; exact_mod_cast hE)

/-- **The Lander–Parkin–Selfridge conjecture implies its `five_three` variant** (`k = 5`,
`n = 3`, `m = 1`). The values on the two sides differ because `y ^ 5` exceeds each `xᵢ ^ 5`. -/
theorem five_three_of_lps (h : LanderParkinSelfridgeConjecture) : LPSFiveThree := by
  intro x₁ x₂ x₃ y h1 h2 h3 hy hE
  have p1 : 0 < x₁ ^ 5 := by positivity
  have p2 : 0 < x₂ ^ 5 := by positivity
  have p3 : 0 < x₃ ^ 5 := by positivity
  have n1 : x₁ ≠ y := by rintro rfl; omega
  have n2 : x₂ ≠ y := by rintro rfl; omega
  have n3 : x₃ ≠ y := by rintro rfl; omega
  have := h 5 3 1 ![x₁, x₂, x₃] ![y] (by norm_num) one_pos
    (by simp [Fin.forall_fin_succ]; omega) (by simp; omega)
    (by simp [Fin.forall_fin_succ]; omega) (by simp [Fin.sum_univ_succ]; omega)
  omega

end Implications.Misc.LPS324
