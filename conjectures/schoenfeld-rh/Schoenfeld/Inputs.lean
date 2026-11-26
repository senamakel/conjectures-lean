import Mathlib

/-!
# Cited numerical inputs (tier H)

The sharp constant `1/(8π)` needs two published numerical facts that this repository does not
re-prove. Both have complete Lean proofs elsewhere (on older toolchains); each enters here as a
named `Prop`, so every theorem that uses one states it as a hypothesis.

* `RosserZeroCount`: Rosser's explicit Riemann–von Mangoldt formula (J. B. Rosser, *Explicit
  bounds for some functions of prime numbers*, Amer. J. Math. 63 (1941), Theorem 19):
  `|N(T) − (T/2π) log(T/2π) + T/2π − 7/8| < 0.137 log T + 0.443 log log T + 1.588` for `T ≥ 2`.
  `positiveZeroCount` and the statement are copied verbatim from
  `TernaryGoldbach.RSBounds.Rosser1941` in
  [teorth/IEANTN](https://github.com/teorth/IEANTN)
  (`Solutions/Schoenfeld1976Numerics.v1/Proof/RSBounds/RosserCountDefinition.lean` and
  `Rosser1941.lean`, commit `cd9c2dd`, Apache-2.0), where
  `Rosser1941.zero_count_bounds` proves it unconditionally (Backlund's argument from height 100,
  certified zeros below), on Lean `v4.34.0-rc2`.
* `PsiCert`: `|ψ(x) − x| ≤ (4/5)√x` for `1500 ≤ x ≤ 10¹⁰`, copied verbatim from
  `Goals.Schoenfeld1976.PsiCert` in [Garald1/RSBounds](https://github.com/Garald1/RSBounds)
  (`RSBounds/Schoenfeld1976TargetsExtra.lean`, commit `82d7a55`, Apache-2.0), whose
  kernel-checked campaign `PsiFinite.psi_abs_sub_le_four_fifths_sqrt` proves it, on Lean
  `v4.35.0`.
-/

namespace Schoenfeld

open Complex Real

/-- Zeta zeros with positive ordinate at most `T`, counted with multiplicity.
Zero order vanishes at every point where zeta is nonzero.

(Verbatim from IEANTN's `TernaryGoldbach.RSBounds.Rosser1941.positiveZeroCount`.) -/
noncomputable def positiveZeroCount (T : ℝ) : ℝ := by
  classical
  exact ∑' ρ : ℂ, if 0 < ρ.im ∧ ρ.im ≤ T then
    ((analyticOrderAt riemannZeta ρ).toNat : ℝ) else 0

/-- Rosser (1941), Theorem 19: the statement of IEANTN's `Rosser1941.zero_count_bounds`. -/
def RosserZeroCount : Prop :=
  ∀ T : ℝ, 2 ≤ T →
    |positiveZeroCount T -
      (T / (2 * Real.pi) * Real.log (T / (2 * Real.pi)) - T / (2 * Real.pi) + 7 / 8)| <
      0.137 * Real.log T + 0.443 * Real.log (Real.log T) + 1.588

/-- `|ψ(x) − x| ≤ (4/5)√x` on `[1500, 10¹⁰]` (verbatim from RSBounds'
`Goals.Schoenfeld1976.PsiCert`). -/
def PsiCert : Prop :=
  ∀ x : ℝ, 1500 ≤ x → x ≤ 10 ^ 10 → |Chebyshev.psi x - x| ≤ 4 / 5 * Real.sqrt x

end Schoenfeld
