import Artin.Analytic.Interface

/-!
# Hecke's analytic continuation of `ζ_K`, as a hypothesis

`HooleyHypothesis` (through `IsDedekindZeta`) only constrains functions `Z` that are holomorphic
on `ℂ ∖ {1}` and agree with `ζ_K` on `Re s > 1`. To use it we need such a `Z`, that is, the
analytic continuation of `ζ_K`, together with the functional equation and some growth, which the
explicit formula needs. None of this is in our Mathlib pin or in upstream Mathlib. Following
the erdos-985 precedent, the main library takes it as an explicit hypothesis,
`DedekindContinuation K`; a separate `Unconditional/` module can later discharge it from a
formalisation of Hecke's theorem (e.g. leanprover-community/riemann-hypothesis, Tate's thesis).

## The statement

For a number field `K` of degree `n = r₁ + 2 r₂` and discriminant `d_K`, write
`γ_K(s) = |d_K|^{s/2} Γ_ℝ(s)^{r₁} Γ_ℂ(s)^{r₂}` (`gammaFactorK`) and, for a function `Z`,
`Λ_Z(s) = γ_K(s) Z(s)` (`completedOf`). `ContinuationData K` bundles

* `Z`, with `IsDedekindZeta K Z`: holomorphic on `ℂ ∖ {1}`, equal to `dedekindZeta K` on
  `Re s > 1`;
* `ξ`, entire, with `ξ(s) = s (s - 1) Λ_Z(s)` for `Re s > 0`, `s ≠ 1`;
* the functional equation `ξ(1 - s) = ξ(s)`;
* growth in the strip: `‖ξ(s)‖ ≤ M (1 + ‖s‖)²` for `1/2 ≤ Re s ≤ 2`.

These are Hecke's theorem (Hecke 1917; Tate's thesis 1950; Neukirch, *Algebraic Number Theory*,
VII.5.11; Lang, *Algebraic Number Theory*, XIII.3, Theorem 3), in the following form.

* `s (s - 1) Λ_K(s)` is entire and `Λ_K(1 - s) = Λ_K(s)`. Since
  `ξ(1 - s) = (1 - s)(-s) Λ_K(1 - s) = s (s - 1) Λ_K(1 - s)`, the functional equation of `Λ_K`
  is that of `ξ`. We state it for `ξ` because Lean's `Gamma` takes the junk value `0` at its
  poles, so the pointwise product `γ_K(s) Z(s)` is not the completed function at the
  non-positive integers, where `Γ` has poles and `Z` has its trivial zeros. For the same reason
  the identity `ξ = s (s - 1) Λ_Z` is only asked for `Re s > 0`, where `γ_K` has no poles; by the
  identity theorem it pins `ξ` down.
* Hecke's integral representation
  `Λ_K(s) = R/(s - 1) - R/s + ∫_1^∞ (θ_K(t) - c)(t^{s/2} + t^{(1-s)/2}) dt/t` shows that
  `Λ_K(s) - R/(s - 1) + R/s` is bounded in every vertical strip, so
  `ξ(s) = R + s (s - 1) (…) = O((1 + |s|)²)` there. We only ask for the strip
  `1/2 ≤ Re s ≤ 2`: the functional equation gives `-1 ≤ Re s ≤ 1/2`, and to the right of
  `Re s = 2` the Euler product and Stirling's bound for `Γ` take over. That is enough to show
  that `ξ` has order `1` (`Artin/Analytic/Core/Xi.lean`), which the Hadamard product needs.

The riemann-hypothesis repository proves (unlicensed, so nothing is copied from it):
`differentiableAt_completedDedekindZeta` (`Λ_K` holomorphic off `{0, 1}`),
`completedDedekindZeta_one_sub` (the functional equation),
`tendsto_sub_one_mul_completedDedekindZeta_rootNumber` and `tendsto_mul_completedDedekindZeta_zero`
(simple poles at `1` and `0`, hence `ξ` extends to an entire function), and
`continuedDedekindZeta_eq`, `differentiableAt_continuedDedekindZeta` (a `Z` with
`IsDedekindZeta K Z`). Those give every field of `ContinuationData` except the strip bound.
It builds `Λ_K` as the `Λ` of a Mathlib `WeakFEPair` (`thetaPair`), and the strip bound follows
from that representation alone: `Artin/Analytic/ContinuationOfFEPair.lean` proves it with
Mathlib only, and `Unconditional/ArtinUnconditional.lean` discharges `DedekindContinuation K`
for every number field by importing the Tate-thesis modules of that repository.

Things that are *not* part of the hypothesis, because they follow from it (with the Euler
product) and are proved, or stated as separate lemmas, in `Artin/Analytic/Core/`: `ζ_K(s) ≠ 0`
for `Re s ≥ 1`, the simple pole at `s = 1` with Mathlib's residue
(`NumberField.tendsto_sub_one_mul_dedekindZeta_nhdsGT`), and the order of `ξ`.
-/

namespace Artin.Analytic

open NumberField Complex ArtinPrimitiveRootsConjecture

section

variable (K : Type*) [Field K] [NumberField K]

/-- The archimedean factor of `ζ_K`, including the discriminant:
`γ_K(s) = |d_K|^{s/2} Γ_ℝ(s)^{r₁} Γ_ℂ(s)^{r₂}`. -/
noncomputable def gammaFactorK (s : ℂ) : ℂ :=
  (((|(discr K : ℝ)| : ℝ)) : ℂ) ^ (s / 2) * Gammaℝ s ^ InfinitePlace.nrRealPlaces K *
    Gammaℂ s ^ InfinitePlace.nrComplexPlaces K

/-- The completed function attached to `Z`: `Λ_Z(s) = γ_K(s) Z(s)`. For `Z` the continuation of
`ζ_K` this is `Λ_K` wherever the Gamma factors have no pole (in particular for `Re s > 0`). -/
noncomputable def completedOf (Z : ℂ → ℂ) (s : ℂ) : ℂ :=
  gammaFactorK K s * Z s

/-- **Hecke's theorem, as data.** A continuation `Z` of `ζ_K` to `ℂ ∖ {1}`, and the entire
function `ξ(s) = s (s - 1) Λ_K(s)`, with the functional equation and polynomial growth in the
strip `1/2 ≤ Re s ≤ 2`. See the module docstring for why each field is stated as it is. -/
structure ContinuationData where
  /-- The analytic continuation of `ζ_K`. -/
  Z : ℂ → ℂ
  isDedekindZeta : IsDedekindZeta K Z
  /-- `ξ_K(s) = s (s - 1) Λ_K(s)`, extended to an entire function. -/
  ξ : ℂ → ℂ
  differentiable_ξ : Differentiable ℂ ξ
  ξ_eq : ∀ s : ℂ, 0 < s.re → s ≠ 1 → ξ s = s * (s - 1) * completedOf K Z s
  ξ_one_sub : ∀ s : ℂ, ξ (1 - s) = ξ s
  strip_bound : ∃ M : ℝ, ∀ s : ℂ, 1 / 2 ≤ s.re → s.re ≤ 2 → ‖ξ s‖ ≤ M * (1 + ‖s‖) ^ 2

/-- **Hecke's analytic continuation and functional equation for `ζ_K`**, as a hypothesis:
there is a continuation `Z` of `ζ_K` to `ℂ ∖ {1}` such that `ξ(s) = s (s - 1) Λ_Z(s)`, with
`Λ_Z(s) = |d_K|^{s/2} Γ_ℝ(s)^{r₁} Γ_ℂ(s)^{r₂} Z(s)`, extends to an entire function with
`ξ(1 - s) = ξ(s)` and `‖ξ(s)‖ ≤ M (1 + ‖s‖)²` for `1/2 ≤ Re s ≤ 2`. -/
def DedekindContinuation : Prop :=
  Nonempty (ContinuationData K)

end

end Artin.Analytic
