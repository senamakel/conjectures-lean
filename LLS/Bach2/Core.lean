import LLS.Bach2.Sound
import LLS.Bach2.Tail2
import LLS.BachCore
import Ankeny.Finite

/-!
# From a certified modulus to Bach's bound with constant `2`

`Good2 q` (what the checker certifies) gives, under GRH, a unit of residue `≤ 2 log² q` outside
every proper subgroup of `(ZMod q)ˣ`: either the units of residue `≤ x ≤ 2 log² q` generate the
whole group, or a character `χ ≠ 1` trivial on the subgroup would make a budget non-positive.
-/

namespace LLS

open Erdos985 (DirichletLNonvanishingRightOfHalf)

theorem bach_of_good2 (hGRH : DirichletLNonvanishingRightOfHalf) (q : ℕ) [NeZero q]
    (hq : Good2 q) (H : Subgroup (ZMod q)ˣ) (hH : H ≠ ⊤) :
    ∃ a : (ZMod q)ˣ, a ∉ H ∧ ((a : ZMod q).val : ℝ) ≤ 2 * Real.log q ^ 2 := by
  obtain ⟨x, hxq, hgen | ⟨hx64, Pc, hPc, hpos⟩⟩ := hq
  · by_contra hcon
    push Not at hcon
    apply hH
    rw [eq_top_iff, ← hgen, Subgroup.closure_le]
    intro u hu
    by_contra huH
    have h1 := hcon u huH
    have h2 : ((u : ZMod q).val : ℝ) ≤ x := by exact_mod_cast hu
    linarith
  · by_contra hcon
    push Not at hcon
    obtain ⟨χ, hχ, hχH⟩ := Ankeny.exists_dirichletCharacter_trivial_on H hH
    have hval : ∀ n ≤ x, n.Coprime q → χ n = 1 := by
      intro n hn hcop
      set u := ZMod.unitOfCoprime n hcop
      have hu : u ∈ H := by
        by_contra hu
        have h1 := hcon u hu
        have e : (u : ZMod q).val = n % q := by simp [u, ZMod.val_natCast]
        have : ((n % q : ℕ) : ℝ) ≤ x := by exact_mod_cast (Nat.mod_le n q).trans hn
        rw [e] at h1
        linarith
      simpa [u] using hχH u hu
    rcases hpos with hQ | ⟨hβκ, hU⟩
    · have := budgetQ_nonpos hGRH χ hχ x hx64 hval Pc hPc
      linarith
    · have := budgetU_nonpos hGRH χ hχ x hx64 hval Pc hPc 53 (by norm_num) hβκ
      linarith

/-- Bach's bound for `q ≥ 2^2500`, from the uniform budget `LLS.Phi` and `goodQ_tail2`. -/
theorem bach_tail2 (hGRH : DirichletLNonvanishingRightOfHalf) (q : ℕ) [NeZero q]
    (hq : 2 ^ 2500 ≤ q) (H : Subgroup (ZMod q)ˣ) (hH : H ≠ ⊤) :
    ∃ a : (ZMod q)ˣ, a ∉ H ∧ ((a : ZMod q).val : ℝ) ≤ 2 * Real.log q ^ 2 :=
  bach_of_goodQ hGRH q (goodQ_tail2 q hq) H hH

end LLS
