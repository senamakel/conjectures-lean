import Grosswald.Statement
import Grosswald.Sieve
import Erdos985.Analytic.ExplicitFormula
import Erdos985.Analytic.Principal

/-!
# The analytic input at `x = ⌊√p⌋ - 2`

Under GRH, if `p` has no prime primitive root below `√p - 2`, then for every admissible set `S`
of sieving primes the inequality `SieveIneq ω(p-1) |S| δ_S p` *fails*. Everything after this
file is arithmetic and computation.
-/

namespace Grosswald

open ArithmeticFunction Erdos985

/-- `x = ⌊√p⌋ - 2`; a prime `q < x` satisfies `q < √p - 2`. -/
def xOf (p : ℕ) : ℕ := Nat.sqrt p - 2

/-- The sieve constant `2^{n-s} (2 + (s-1)/δ) - 1` of MTT Theorem 3. -/
noncomputable def sieveK (n s : ℕ) (δ : ℝ) : ℝ := 2 ^ (n - s) * (2 + ((s : ℝ) - 1) / δ) - 1

/-- `δ_S = 1 - Σ_{ℓ ∈ S} 1/ℓ`. -/
noncomputable def deltaOf (S : Finset ℕ) : ℝ := 1 - ∑ ℓ ∈ S, 1 / (ℓ : ℝ)

/-- The inequality that contradicts the sieve: `K · c(p,x) √x log p < x/2 - (√x/20 + 3)`. -/
def SieveIneq (n s : ℕ) (δ : ℝ) (p : ℕ) : Prop :=
  sieveK n s δ * (bachC p (xOf p) * √(xOf p : ℝ) * Real.log p)
    < (xOf p : ℝ) / 2 - (√(xOf p : ℝ) / 20 + 3)

lemma lt_sqrt_sub_two_of_lt_xOf {p q : ℕ} (h : q < xOf p) : (q : ℝ) < √(p : ℝ) - 2 := by
  have h1 : q + 3 ≤ Nat.sqrt p := by unfold xOf at h; omega
  have h2 : ((q + 3 : ℕ) : ℝ) ≤ Nat.sqrt p := by exact_mod_cast h1
  have h3 := Real.nat_sqrt_le_real_sqrt (a := p)
  push_cast at h2
  linarith

/-- Under GRH, a prime with no prime primitive root below `√p - 2` violates every sieve
inequality. -/
theorem not_sieveIneq_of_GRH (hGRH : DirichletLNonvanishingRightOfHalf) {p : ℕ} (hp : p.Prime)
    (hp9 : 9 ≤ p) (hno : ¬ HasSmallPrimePrimitiveRoot p) {S : Finset ℕ}
    (hS : S ⊆ (p - 1).primeFactors) (hδ : 0 < deltaOf S) :
    ¬ SieveIneq (p - 1).primeFactors.card S.card (deltaOf S) p := by
  have : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := by omega
  set x := xOf p with hx
  have hsq : 3 ≤ Nat.sqrt p := Nat.le_sqrt.mpr (by omega)
  have hx1 : 1 ≤ x := by simp only [hx, xOf]; omega
  have hxp : x ≤ p := by simp only [hx, xOf]; have := Nat.sqrt_le_self p; omega
  have hno' : ∀ q, q.Prime → q < x → orderOf (q : ZMod p) ≠ p - 1 := by
    intro q hq hqx hord
    exact hno ⟨q, hq, lt_sqrt_sub_two_of_lt_xOf hqx, hord⟩
  have key := Sieve.principal_le_sieve p hp2 x hxp (bachC p x * √(x : ℝ) * Real.log p)
    (fun χ hχ => Analytic.bach_nonprincipal_of_GRH hGRH p χ hχ x hx1) hno' S hS hδ
  have hprin := (abs_le.mp (Analytic.bach_principal_of_GRH hGRH x hx1)).1
  intro hineq
  unfold SieveIneq sieveK deltaOf at hineq
  unfold deltaOf at hδ
  rw [← hx] at hineq
  linarith

end Grosswald
