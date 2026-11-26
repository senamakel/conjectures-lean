import Mathlib
import Erdos985.Statement

/-!
# Target statements (fixed once written; do not edit to make a proof go through)

Source: Y. Lamzouri, X. Li, K. Soundararajan, *Conditional bounds for the least quadratic
non-residue and related problems*, Math. Comp. 84 (2015), 2391–2412, arXiv:1309.3595 (the
statements below are read from the corrected arXiv source `QuaResL1Corrected.tex`, v3, 2016).
All results there assume GRH for Dirichlet `L`-functions; in Lean that hypothesis is
`Erdos985.DirichletLNonvanishingRightOfHalf`, copied word for word in erdos-985 from
leanprover-community/riemann-hypothesis `src/Statements.lean`, and it is never restated here.

The definitions are the paper's statements, transcribed literally:

* `LLS.A`, `LLS.B`, `LLS.LeastPrimeOutsideSubgroup`: Theorem 1.1 (1).
* `LLS.LeastPrimeOutsideSubgroupRough`: Theorem 1.1 (2).
* `LLS.LeastNonresidueBelowLogSq`: Corollary 1.2.
* `LLS.LeastPrimeInCoset`: Theorem 1.4.
* `LLS.L1UpperBound`, `LLS.L1LowerBound`: Theorem 1.5.

Conventions. `ω(q)` is `q.primeFactors.card`; `Σ_{p | q}` is a sum over `q.primeFactors`;
`L(1, χ)` is Mathlib's `DirichletCharacter.LFunction χ 1`; `γ` is `Real.eulerMascheroniConstant`.
"`ℓ` lies in `H`" for a prime `ℓ ∤ q` means that its unit `ZMod.unitOfCoprime ℓ _` lies in `H`.
-/

namespace LLS

open Real

/-- Theorem 1.1's `A(q) = max(0, 2 log log q − 8/5 − Σ_{p | q} (log p)/(p − 1))`. -/
noncomputable def A (q : ℕ) : ℝ :=
  max 0 (2 * log (log q) - 8 / 5 - ∑ p ∈ q.primeFactors, log p / ((p : ℝ) - 1))

/-- Theorem 1.1's
`B(q) = max(0, 2 log log q + 3 + 2 ω(q) (log log q)² / log q − 2 A(q))`. -/
noncomputable def B (q : ℕ) : ℝ :=
  max 0 (2 * log (log q) + 3
    + 2 * (q.primeFactors.card : ℝ) * log (log q) ^ 2 / log q - 2 * A q)

/-- **LLS Theorem 1.1 (1)**. For `q ≥ 3000` and a proper subgroup `H` of `(ℤ/qℤ)ˣ`, the least
prime `ℓ ∤ q` not lying in `H` satisfies `ℓ ≤ (log q + B(q))²`. -/
def LeastPrimeOutsideSubgroup : Prop :=
  ∀ q : ℕ, 3000 ≤ q → ∀ H : Subgroup (ZMod q)ˣ, H ≠ ⊤ →
    ∃ ℓ : ℕ, ℓ.Prime ∧ ∃ hℓ : ℓ.Coprime q,
      ZMod.unitOfCoprime ℓ hℓ ∉ H ∧ (ℓ : ℝ) ≤ (log q + B q) ^ 2

/-- **LLS Theorem 1.1 (2)**. If `q ≥ 3000` is not divisible by any prime below `(log q)²`,
then some prime `ℓ ≤ (log q)²` does not lie in `H`. (Such an `ℓ` is automatically prime to
`q`, except when `ℓ = (log q)²` exactly; we ask for `ℓ ∤ q` explicitly.) -/
def LeastPrimeOutsideSubgroupRough : Prop :=
  ∀ q : ℕ, 3000 ≤ q → (∀ p : ℕ, p.Prime → p ∣ q → log q ^ 2 ≤ p) →
    ∀ H : Subgroup (ZMod q)ˣ, H ≠ ⊤ →
      ∃ ℓ : ℕ, ℓ.Prime ∧ ∃ hℓ : ℓ.Coprime q,
        ZMod.unitOfCoprime ℓ hℓ ∉ H ∧ (ℓ : ℝ) ≤ log q ^ 2

/-- **LLS Corollary 1.2**. If `q ≥ 5` is prime, the least quadratic non-residue mod `q` lies
below `(log q)²`. -/
def LeastNonresidueBelowLogSq : Prop :=
  ∀ q : ℕ, q.Prime → 5 ≤ q →
    ∃ n : ℕ, 0 < n ∧ (n : ℝ) ≤ log q ^ 2 ∧ ¬ IsSquare (n : ZMod q)

/-- **LLS Theorem 1.4**. For `q ≥ 20000`, a subgroup `H` of `(ℤ/qℤ)ˣ` of index `h > 1` and a
coset `aH`, the least prime `p` in `aH` satisfies `p ≤ 10⁹` or
`p ≤ ((h − 1) log q + 3(h + 1) + (5/2)(log log q)²)²`. -/
def LeastPrimeInCoset : Prop :=
  ∀ q : ℕ, 20000 ≤ q → ∀ H : Subgroup (ZMod q)ˣ, 1 < H.index → ∀ a : (ZMod q)ˣ,
    ∃ p : ℕ, p.Prime ∧ ∃ hp : p.Coprime q, a⁻¹ * ZMod.unitOfCoprime p hp ∈ H ∧
      ((p : ℝ) ≤ 10 ^ 9 ∨
        (p : ℝ) ≤ ((H.index - 1 : ℝ) * log q + 3 * (H.index + 1 : ℝ)
          + 5 / 2 * log (log q) ^ 2) ^ 2)

/-- **LLS Theorem 1.5**, upper bound. For `q ≥ 10¹⁰` and `χ` primitive mod `q`,
`|L(1, χ)| ≤ 2 e^γ (log log q − log 2 + 1/2 + 1/log log q)`. -/
def L1UpperBound : Prop :=
  ∀ (q : ℕ) [NeZero q], (10 : ℝ) ^ 10 ≤ q → ∀ χ : DirichletCharacter ℂ q, χ.IsPrimitive →
    ‖DirichletCharacter.LFunction χ 1‖
      ≤ 2 * exp eulerMascheroniConstant
          * (log (log q) - log 2 + 1 / 2 + 1 / log (log q))

/-- **LLS Theorem 1.5**, lower bound. For `q ≥ 10¹⁰` and `χ` primitive mod `q`,
`1/|L(1, χ)| ≤ (12 e^γ/π²)(log log q − log 2 + 1/2 + 1/log log q + 14 log log q / log q)`. -/
def L1LowerBound : Prop :=
  ∀ (q : ℕ) [NeZero q], (10 : ℝ) ^ 10 ≤ q → ∀ χ : DirichletCharacter ℂ q, χ.IsPrimitive →
    1 / ‖DirichletCharacter.LFunction χ 1‖
      ≤ 12 * exp eulerMascheroniConstant / π ^ 2
          * (log (log q) - log 2 + 1 / 2 + 1 / log (log q) + 14 * log (log q) / log q)

end LLS
