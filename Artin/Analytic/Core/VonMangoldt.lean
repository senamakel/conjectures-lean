import Artin.Analytic.Splitting
import Artin.Analytic.Continuation

/-!
# The von Mangoldt function of a number field

`Λ_K(n) = ∑_{𝔭, m ≥ 1, N𝔭^m = n} log N𝔭`, so that `ψ_K(x) = ∑_{n < x} Λ_K(n)` (`psiK_eq_sum`)
and `-ζ_K'/ζ_K(s) = ∑ Λ_K(n) n^{-s}` for `Re s > 1` (`LSeries_vonMangoldtK`).

* `vonMangoldtK_le`: `Λ_K(n) ≤ [K : ℚ] Λ(n)`. For `n = p^j` the ideals `𝔭^m` of norm `p^j` have
  `f(𝔭) m = j`, each contributes `f(𝔭) log p`, and `∑_{𝔭 ∣ p} f(𝔭) ≤ ∑ e f = [K : ℚ]`.
* `LSeries_vonMangoldtK` and `dedekindZeta_ne_zero` are the Euler product of `ζ_K`
  (unique factorisation of ideals); both are left as `sorry` here, see their docstrings.
-/

namespace Artin.Analytic

open NumberField Finset ArithmeticFunction

variable (K : Type*) [Field K] [NumberField K]

/-- The von Mangoldt function of `K`: `Λ_K(n) = ∑_{𝔭, m ≥ 1, N𝔭^m = n} log N𝔭`, the sum over
prime ideals `𝔭` (grouped by the rational prime `p` below them) and exponents `m ≥ 1`. The ranges
`p ≤ n` and `m ≤ n` are no restriction, since `N𝔭^m ≥ p` and `N𝔭^m ≥ 2^m > m`. -/
noncomputable def vonMangoldtK (n : ℕ) : ℝ :=
  ∑ p ∈ (range (n + 1)).filter Nat.Prime, ∑ P ∈ primesAbove K p, ∑ m ∈ Icc 1 n,
    if Ideal.absNorm P ^ m = n then Real.log (Ideal.absNorm P) else 0

lemma vonMangoldtK_nonneg (n : ℕ) : 0 ≤ vonMangoldtK K n := by
  unfold vonMangoldtK
  refine sum_nonneg fun p _ => sum_nonneg fun P _ => sum_nonneg fun m _ => ?_
  split_ifs
  · exact Real.log_natCast_nonneg _
  · exact le_rfl

/-- `ψ_K(x) = ∑_{n < x} Λ_K(n)`, the sum over `n < ⌈x⌉`. Both sides run over the pairs
`(𝔭, m)` with `N𝔭^m < x`. -/
theorem psiK_eq_sum {x : ℝ} (hx : 0 ≤ x) :
    psiK K x = ∑ n ∈ range ⌈x⌉₊, vonMangoldtK K n := by
  sorry

theorem psiK_natCast_eq_sum (x : ℕ) : psiK K x = ∑ n ∈ range x, vonMangoldtK K n := by
  rw [psiK_eq_sum K (Nat.cast_nonneg x), Nat.ceil_natCast]

/-- `Λ_K(n) ≤ [K : ℚ] Λ(n)`. -/
theorem vonMangoldtK_le (n : ℕ) : vonMangoldtK K n ≤ Module.finrank ℚ K * Λ n := by
  sorry

/-- The Dirichlet series of `Λ_K` converges absolutely for `Re s > 1`. -/
theorem LSeriesSummable_vonMangoldtK {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable (fun n => (vonMangoldtK K n : ℂ)) s := by
  have h := (LSeriesSummable_vonMangoldt hs).norm.mul_left (Module.finrank ℚ K : ℝ)
  refine Summable.of_norm_bounded h fun n => ?_
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  rw [LSeries.norm_term_eq, LSeries.norm_term_eq, if_neg hn, if_neg hn, Complex.norm_real,
    Real.norm_of_nonneg (vonMangoldtK_nonneg K n), Complex.norm_real,
    Real.norm_of_nonneg vonMangoldt_nonneg, ← mul_div_assoc]
  gcongr
  exact vonMangoldtK_le K n

/-- **Euler product, logarithmic derivative form**: `-ζ_K'(s)/ζ_K(s) = ∑ Λ_K(n) n^{-s}` for
`Re s > 1`. Standard (e.g. Neukirch, *Algebraic Number Theory*, VII.5.1, or Lang, *Algebraic
Number Theory*, VIII.2): `ζ_K(s) = ∏_𝔭 (1 - N𝔭^{-s})^{-1}` by unique factorisation of ideals,
then take the logarithmic derivative term by term. Mathlib has the Euler product machinery for
`LSeries` of multiplicative functions (`LSeries_eulerProduct`), but not this instance. -/
theorem LSeries_vonMangoldtK {s : ℂ} (hs : 1 < s.re) :
    LSeries (fun n => (vonMangoldtK K n : ℂ)) s =
      -(deriv (dedekindZeta K) s / dedekindZeta K s) := by
  sorry

/-- **`ζ_K` has no zeros for `Re s > 1`**, from the Euler product (same references as
`LSeries_vonMangoldtK`): a convergent product of non-zero factors. -/
theorem dedekindZeta_ne_zero {s : ℂ} (hs : 1 < s.re) : dedekindZeta K s ≠ 0 := by
  sorry

end Artin.Analytic
