import Mathlib
import Erdos985.Statement

/-!
# Target statements: primes in arithmetic progressions under GRH

These are the fixed targets of the repository. No formal-conjectures statement exists for them,
so they are transcribed from Montgomery–Vaughan, *Multiplicative Number Theory I* (Cambridge
2007), Theorem 13.7 and Corollary 13.8, which attribute them to Titchmarsh (1930). See also
Davenport, *Multiplicative Number Theory*, Chapter 20.

The hypothesis is `Erdos985.DirichletLNonvanishingRightOfHalf` (GRH for all Dirichlet
L-functions), copied verbatim from `src/Statements.lean` of leanprover-community/riemann-hypothesis.

Conventions.
* `psiChar χ x = ψ(x, χ) = Σ_{n ≤ x} Λ(n) χ(n)`.
* `mainTerm χ x = E₀(χ) x`, where `E₀(χ) = 1` for the principal character (Mathlib's `1`) and `0`
  otherwise.
* `psiAP q a x = ψ(x; q, a)`, `thetaAP q a x = ϑ(x; q, a)`, `primeCountAP q a x = π(x; q, a)`.
* `li x = ∫₂ˣ dt / log t`, the offset logarithmic integral. It differs from the principal-value
  integral `∫₀ˣ` by the constant `li(2) ≈ 1.045`, which every error term below absorbs.

All the bounds are uniform in the modulus `q`: one absolute constant `C` serves every `q ≥ 1`,
every character mod `q`, every residue class, and every `x ≥ 2`.
-/

namespace PsiGRH

open ArithmeticFunction

/-- `ψ(x, χ) = Σ_{1 ≤ n ≤ x} Λ(n) χ(n)`. -/
noncomputable def psiChar {N : ℕ} (χ : DirichletCharacter ℂ N) (x : ℝ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (Λ n : ℂ) * χ n

open scoped Classical in
/-- The main term `E₀(χ) x`: `x` for the principal character, `0` for every other one. -/
noncomputable def mainTerm {N : ℕ} (χ : DirichletCharacter ℂ N) (x : ℝ) : ℂ :=
  if χ = 1 then (x : ℂ) else 0

/-- `ψ(x; q, a) = Σ_{n ≤ x, n ≡ a (mod q)} Λ(n)`. -/
noncomputable def psiAP (q a : ℕ) (x : ℝ) : ℝ :=
  ∑ n ∈ (Finset.Icc 1 ⌊x⌋₊).filter (fun n => n ≡ a [MOD q]), Λ n

/-- `ϑ(x; q, a) = Σ_{p ≤ x, p ≡ a (mod q)} log p`. -/
noncomputable def thetaAP (q a : ℕ) (x : ℝ) : ℝ :=
  ∑ p ∈ (Finset.Icc 1 ⌊x⌋₊).filter (fun p => p.Prime ∧ p ≡ a [MOD q]), Real.log p

/-- `π(x; q, a)`, the number of primes `p ≤ x` with `p ≡ a (mod q)`. -/
noncomputable def primeCountAP (q a : ℕ) (x : ℝ) : ℕ :=
  ((Finset.Icc 1 ⌊x⌋₊).filter (fun p => p.Prime ∧ p ≡ a [MOD q])).card

/-- The offset logarithmic integral `li(x) = ∫₂ˣ dt / log t`. -/
noncomputable def li (x : ℝ) : ℝ :=
  ∫ t in (2 : ℝ)..x, 1 / Real.log t

/-! ### Characters -/

/-- Montgomery–Vaughan (13.19) with constant `C`:
`|ψ(x, χ) − E₀(χ) x| ≤ C √x (log x) (log qx)` for every `q ≥ 1`, every character `χ` mod `q`
and every `x ≥ 2`. -/
def PsiCharBound (C : ℝ) : Prop :=
  ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (x : ℝ), 2 ≤ x →
    ‖psiChar χ x - mainTerm χ x‖ ≤ C * Real.sqrt x * Real.log x * Real.log (q * x)

/-- Montgomery–Vaughan Theorem 13.7, (13.19): under GRH,
`ψ(x, χ) = E₀(χ) x + O(√x (log x)(log qx))`, uniformly in `q`. -/
def PsiCharStatement : Prop :=
  ∃ C : ℝ, 0 < C ∧ PsiCharBound C

/-- The weaker shape `|ψ(x, χ) − E₀(χ) x| ≤ C √x log²(qx)` (Davenport, Ch. 20), with constant
`C`. It follows from `PsiCharBound C` because `log x ≤ log qx`. -/
def PsiCharLogSqBound (C : ℝ) : Prop :=
  ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (x : ℝ), 2 ≤ x →
    ‖psiChar χ x - mainTerm χ x‖ ≤ C * Real.sqrt x * Real.log (q * x) ^ 2

/-- Under GRH, `ψ(x, χ) = E₀(χ) x + O(√x log²(qx))`, uniformly in `q`. -/
def PsiCharLogSqStatement : Prop :=
  ∃ C : ℝ, 0 < C ∧ PsiCharLogSqBound C

/-! ### Arithmetic progressions -/

/-- `|ψ(x; q, a) − x/φ(q)| ≤ C √x (log x)(log qx)` for `q ≥ 1`, `gcd(a, q) = 1`, `x ≥ 2`. -/
def PsiAPBound (C : ℝ) : Prop :=
  ∀ (q a : ℕ), 1 ≤ q → a.Coprime q → ∀ x : ℝ, 2 ≤ x →
    |psiAP q a x - x / q.totient| ≤ C * Real.sqrt x * Real.log x * Real.log (q * x)

/-- Under GRH, `ψ(x; q, a) = x/φ(q) + O(√x (log x)(log qx))`, uniformly in `q`
(Montgomery–Vaughan Corollary 13.8, (13.22), in the form its proof gives before `q ≤ √x` is
used). -/
def PsiAPStatement : Prop :=
  ∃ C : ℝ, 0 < C ∧ PsiAPBound C

/-- `|ϑ(x; q, a) − x/φ(q)| ≤ C √x (log x)(log qx)` for `q ≥ 1`, `gcd(a, q) = 1`, `x ≥ 2`. -/
def ThetaAPBound (C : ℝ) : Prop :=
  ∀ (q a : ℕ), 1 ≤ q → a.Coprime q → ∀ x : ℝ, 2 ≤ x →
    |thetaAP q a x - x / q.totient| ≤ C * Real.sqrt x * Real.log x * Real.log (q * x)

/-- Under GRH, `ϑ(x; q, a) = x/φ(q) + O(√x (log x)(log qx))`, uniformly in `q`
(Montgomery–Vaughan Corollary 13.8, (13.23), same form). -/
def ThetaAPStatement : Prop :=
  ∃ C : ℝ, 0 < C ∧ ThetaAPBound C

/-- `|π(x; q, a) − li(x)/φ(q)| ≤ C √x log(qx)` for `q ≥ 1`, `gcd(a, q) = 1`, `x ≥ 2`. -/
def PiAPBound (C : ℝ) : Prop :=
  ∀ (q a : ℕ), 1 ≤ q → a.Coprime q → ∀ x : ℝ, 2 ≤ x →
    |(primeCountAP q a x : ℝ) - li x / q.totient| ≤ C * Real.sqrt x * Real.log (q * x)

/-- Under GRH, `π(x; q, a) = li(x)/φ(q) + O(√x log(qx))`, uniformly in `q`
(Montgomery–Vaughan (13.21) and (13.24)). -/
def PiAPStatement : Prop :=
  ∃ C : ℝ, 0 < C ∧ PiAPBound C

end PsiGRH
