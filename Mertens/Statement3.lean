import Mertens.Statement

/-!
# Target statements, third batch (fixed once written; see the conjectures tracker, rule 3)

The sharp RH bound for the Mertens function and the bound for `1/ζ` near the half line that it
rests on. Neither has a formal-conjectures counterpart (searched
google-deepmind/formal-conjectures for Mertens, Möbius and `1/ζ` bounds, 2026-11-24), so they
are fixed here.

* `MertensSharpBound`: `M(x) ≤ √x · exp(C log x / log log x)` for large `x`, some absolute `C`.
  Titchmarsh, *A consequence of the Riemann hypothesis*, J. London Math. Soc. 2 (1927) 247–254
  (Landau, Rend. Circ. Mat. Palermo 48 (1924) 277–280, had `M(x) = O(x^{1/2+ε(x)})` with
  `ε(x) ≪ log log log x / log log x`). The attribution is as given by Maier–Montgomery,
  Bull. LMS 41 (2009) 213–226, and Simonič, arXiv:2109.11744; the 1927 paper itself was not
  read. Stronger bounds are known under RH (Maier–Montgomery 2009, Soundararajan 2009); this
  target is the classical one.
* `InvZetaSharpBoundWith c`: `1/|ζ(s)| ≤ exp(C log t / log log t)` for `σ ≥ 1/2 + c/log log t`,
  `t = |Im s|` large. `InvZetaSharpBound` is the case `c = 1`, the form used by Titchmarsh (1927)
  and quoted by Maier–Montgomery (2009) at `σ = 1/2 + 1/log log t`.
-/

namespace Mertens

open Filter

/-- **Titchmarsh (1927)**: `|M(x)| ≤ √x exp(C log x / log log x)` for all large `x`. -/
def MertensSharpBound : Prop :=
  ∃ C x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x →
    |(mertens x : ℝ)| ≤ Real.sqrt x * Real.exp (C * Real.log x / Real.log (Real.log x))

/-- `1/|ζ(s)| ≤ exp(C log t / log log t)` on `σ ≥ 1/2 + c / log log t`, `t = |Im s| ≥ t₀`. -/
def InvZetaSharpBoundWith (c : ℝ) : Prop :=
  ∃ C t₀ : ℝ, ∀ s : ℂ, t₀ ≤ |s.im| →
    1 / 2 + c / Real.log (Real.log |s.im|) ≤ s.re →
      ‖(riemannZeta s)⁻¹‖ ≤ Real.exp (C * Real.log |s.im| / Real.log (Real.log |s.im|))

/-- **Littlewood–Titchmarsh**: the case `c = 1`. -/
def InvZetaSharpBound : Prop := InvZetaSharpBoundWith 1

end Mertens
