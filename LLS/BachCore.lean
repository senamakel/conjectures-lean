import LLS.Numerics.Good
import Ankeny.Statement
import Ankeny.Character

/-!
# From a certified modulus to the subgroup bound

If every unit of residue `≤ x` lies in a proper subgroup `H`, a character `χ ≠ 1` trivial on `H`
satisfies `χ(n) = 1` for all `n ≤ x` prime to `q`, and `Phi_nonpos` gives `Φ(x, log q) ≤ 0`;
`GoodQ c q` provides an `x ≤ c log² q` with `Φ(x, log q) > 0`.
-/

namespace LLS

open Erdos985 (DirichletLNonvanishingRightOfHalf)

theorem bach_of_goodQ (hGRH : DirichletLNonvanishingRightOfHalf) {c : ℝ} (q : ℕ) [NeZero q]
    (hq : GoodQ c q) (H : Subgroup (ZMod q)ˣ) (hH : H ≠ ⊤) :
    ∃ a : (ZMod q)ˣ, a ∉ H ∧ ((a : ZMod q).val : ℝ) ≤ c * Real.log q ^ 2 := by
  obtain ⟨x, hx64, hxc, hPhi, hβκ⟩ := hq
  by_contra hcon
  push Not at hcon
  obtain ⟨χ, hχ, hχH⟩ := Ankeny.exists_dirichletCharacter_trivial_on H hH
  have hval : ∀ n ≤ x, n.Coprime q → χ n = 1 := by
    intro n hn hcop
    set u := ZMod.unitOfCoprime n hcop
    have hu : u ∈ H := by
      by_contra hu
      have h1 := hcon u hu
      have h2 : ((u : ZMod q).val : ℝ) ≤ c * Real.log q ^ 2 := by
        have e : (u : ZMod q).val = n % q := by simp [u, ZMod.val_natCast]
        rw [e]
        have : ((n % q : ℕ) : ℝ) ≤ x := by exact_mod_cast (Nat.mod_le n q).trans hn
        linarith
      linarith
    simpa [u] using hχH u hu
  have := Phi_nonpos hGRH χ hχ x hx64 hval hβκ
  linarith

end LLS
