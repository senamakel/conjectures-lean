import Ankeny.Statement
import Ankeny.Character
import Ankeny.Split

/-!
# Bach's bound for a single modulus, given the numerical inequality

If, with `x = ⌊c log² q⌋`, the key inequality of `Ankeny.Split` fails, then every proper subgroup
of `(ZMod q)ˣ` omits a unit of residue `≤ c log² q`.
-/

namespace Ankeny

open Erdos985

/-- The numerical condition at modulus `q`: the GRH inequality of `key_inequality` fails at
`x = ⌊c log² q⌋`. -/
def NumericOK (c : ℝ) (q : ℕ) : Prop :=
  144 ≤ ⌊c * Real.log q ^ 2⌋₊ ∧
    (√(⌊c * Real.log q ^ 2⌋₊ : ℝ) + 2 + 3 / ⌊c * Real.log q ^ 2⌋₊) * ((2 / 3) * (Real.log q + 5 / 3))
        + (Real.log ⌊c * Real.log q ^ 2⌋₊ + 1) + 0.6
      < (⌊c * Real.log q ^ 2⌋₊ : ℝ) / 2 - √(⌊c * Real.log q ^ 2⌋₊ : ℝ) / 20 - 3
        - q.primeFactors.card * Real.log ⌊c * Real.log q ^ 2⌋₊

theorem bach_of_numericOK (hGRH : DirichletLNonvanishingRightOfHalf) {c : ℝ} (q : ℕ) [NeZero q]
    (hq : NumericOK c q) (H : Subgroup (ZMod q)ˣ) (hH : H ≠ ⊤) :
    ∃ a : (ZMod q)ˣ, a ∉ H ∧ ((a : ZMod q).val : ℝ) ≤ c * Real.log q ^ 2 := by
  by_contra hcon
  push Not at hcon
  obtain ⟨χ, hχ, hχH⟩ := exists_dirichletCharacter_trivial_on H hH
  set x := ⌊c * Real.log q ^ 2⌋₊ with hx
  have hval : ∀ n < x, n.Coprime q → χ n = 1 := by
    intro n hn hcop
    set u := ZMod.unitOfCoprime n hcop
    have hu : u ∈ H := by
      by_contra hu
      have h1 := hcon u hu
      have h2 : ((u : ZMod q).val : ℝ) ≤ c * Real.log q ^ 2 := by
        have e : (u : ZMod q).val = n % q := by
          simp [u, ZMod.val_natCast]
        rw [e]
        have hnx : ((n % q : ℕ) : ℝ) < x := by exact_mod_cast (Nat.mod_le n q).trans_lt hn
        have hxle : (x : ℝ) ≤ c * Real.log q ^ 2 :=
          Nat.floor_le (by
            by_contra hneg
            push Not at hneg
            have : x = 0 := Nat.floor_eq_zero.2 (by linarith)
            have := hq.1
            omega)
        linarith
      linarith
    have := hχH u hu
    simpa [u] using this
  have hkey := key_inequality hGRH χ hχ x hq.1 hval
  have := hq.2
  linarith

end Ankeny
