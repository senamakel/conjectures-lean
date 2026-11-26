import GoldbachAverage.Statement

/-!
# Fujii's theorem (target statements, Round 6; fixed, see the conjectures tracker, rule 3)

A. Fujii, *An additive problem of prime numbers*, Acta Arith. **58** (1991), 173–179: under the
Riemann hypothesis,

  `Σ_{n ≤ x} G(n) = x²/2 + O(x^{3/2})`,   `G(n) = Σ_{a+b=n} Λ(a) Λ(b)`.

Languasco–Zaccagnini, *The number of Goldbach representations of an integer*, Proc. Amer. Math.
Soc. **140** (2012), 795–804 (arXiv:1011.3198), Theorem 1, sharpen this under RH to
`Σ_{n=1}^N R(n) = N²/2 − 2 Σ_ρ N^{ρ+1}/(ρ(ρ+1)) + O(N log³ N)`, and credit the first result of
this kind to Fujii (1991); since `Σ_ρ 1/|ρ(ρ+1)| < ∞`, the zero sum is `O(N^{3/2})` under RH,
which gives the statement above. Their `R(n)` is `goldbachWeight n` (`Λ(0) = 0`).

No formal-conjectures statement exists, so the statements are written here, in the notation of
`GoldbachAverage/Statement.lean` (which is unchanged).
-/

namespace GoldbachAverage

open Filter Asymptotics

/-- **Fujii (1991)**, explicit form: `|S(x) − x²/2| ≤ C x^{3/2}` for all large `x`. -/
def FujiiBound : Prop :=
  ∃ C x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x → |goldbachSum x - x ^ 2 / 2| ≤ C * (x * Real.sqrt x)

/-- **Fujii (1991)**: `S(x) = x²/2 + O(x^{3/2})`. -/
def FujiiStatement : Prop :=
  (fun x : ℝ => goldbachSum x - x ^ 2 / 2) =O[atTop] fun x : ℝ => x ^ ((3 : ℝ) / 2)

end GoldbachAverage
