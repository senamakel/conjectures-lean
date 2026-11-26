# The extended Riemann hypothesis for abelian number fields under GRH in Lean

This repository proves the extended Riemann hypothesis (ERH) for every finite abelian extension
`K/ℚ`: every zero of the Dedekind zeta function `ζ_K` in the critical strip lies on
`Re s = 1/2`. `AbelianERH.Unconditional.abelianERH` proves it unconditionally in Lean, with GRH
for Dirichlet L-functions supplied by the certified proof of L. Alpöge in
[leanprover-community/riemann-hypothesis](https://github.com/leanprover-community/riemann-hypothesis)
and the Kronecker–Weber theorem taken from the same repository. The main library holds a
complete Lean proof that GRH implies ERH for every field that embeds in a cyclotomic field, and,
with Kronecker–Weber as a second hypothesis, for every finite abelian `K/ℚ`.

The argument is the classical factorisation `ζ_K(s) = ∏_{χ ∈ X(K)} L(s, χ)` over the primitive
Dirichlet characters attached to `K` (Washington, *Introduction to Cyclotomic Fields*, 2nd ed.,
1997, Theorem 4.3). It shows that GRH for Dirichlet L-functions implies ERH for every abelian
`K`, and ERH for `ℚ(ζ_N)` gives GRH back for every character mod `N`, so the two statements are
equivalent (label **RH-consequence**; ERH for abelian fields is GRH for Dirichlet L in another
form). Before the 2026 proof of GRH, ERH was open for every abelian field other than `ℚ`, and no
zero-free strip of positive width was known for any `ζ_K`.

```lean
-- Unconditional/AbelianERHUnconditional.lean
theorem AbelianERH.Unconditional.abelianERH : AbelianERH.AbelianERHStatement
theorem AbelianERH.Unconditional.cyclotomicERH : AbelianERH.CyclotomicERHStatement

theorem AbelianERH.abelianERH_of_GRH (hGRH : AbelianERH.DirichletLZerosOnLine)
    (hKW : AbelianERH.KroneckerWeberStatement) : AbelianERH.AbelianERHStatement

theorem AbelianERH.extendedRiemannHypothesis_of_algHom (hGRH : AbelianERH.DirichletLZerosOnLine)
    (K : Type*) [Field K] [NumberField K] {N : ℕ} [NeZero N]
    (φ : K →ₐ[ℚ] CyclotomicField N ℚ) : ERH.ExtendedRiemannHypothesis K

theorem AbelianERH.cyclotomicERH_of_GRH (hGRH : AbelianERH.DirichletLZerosOnLine) :
    AbelianERH.CyclotomicERHStatement

theorem AbelianERH.cyclotomic_extendedRiemannHypothesis_of_GRH (K : Type*) [Field K]
    [NumberField K] (hGRH : AbelianERH.DirichletLZerosOnLine) (N : ℕ) [NeZero N]
    [IsCyclotomicExtension {N} ℚ K] : ERH.ExtendedRiemannHypothesis K

-- the general reduction: ERH for `K` from any coefficient identity `Λ_K = ∑_{χ ∈ X} χ Λ` off `N`
theorem AbelianERH.extendedRiemannHypothesis_of_coeff (K : Type*) [Field K] [NumberField K]
    {N : ℕ} [NeZero N] (hGRH : AbelianERH.DirichletLZerosOnLine)
    {X : Finset (DirichletCharacter ℂ N)} (hX : AbelianERH.CoeffIdentity K X) :
    ERH.ExtendedRiemannHypothesis K
```

The targets, fixed in `AbelianERH/Statement.lean`:

```lean
def ERH.IsDedekindZeta (K : Type*) [Field K] [NumberField K] (Z : ℂ → ℂ) : Prop :=
  DifferentiableOn ℂ Z {1}ᶜ ∧ ∀ s : ℂ, 1 < s.re → Z s = NumberField.dedekindZeta K s

def ERH.ExtendedRiemannHypothesis (K : Type*) [Field K] [NumberField K] : Prop :=
  ∀ Z : ℂ → ℂ, IsDedekindZeta K Z → ∀ s : ℂ, 0 < s.re → s.re < 1 → Z s = 0 → s.re = 1 / 2

def AbelianERH.DirichletLZerosOnLine : Prop :=
  ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (s : ℂ),
    0 < s.re → s.re < 1 → DirichletCharacter.LFunction χ s = 0 → s.re = 1 / 2

def AbelianERH.KroneckerWeberStatement : Prop :=
  ∀ (L : Type) [Field L] [NumberField L] [IsAbelianGalois ℚ L],
    ∃ N : ℕ, 0 < N ∧ Nonempty (L →ₐ[ℚ] CyclotomicField N ℚ)

def AbelianERH.AbelianERHStatement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [IsAbelianGalois ℚ K], ERH.ExtendedRiemannHypothesis K

def AbelianERH.CyclotomicERHStatement : Prop :=
  ∀ (N : ℕ) [NeZero N] (K : Type) [Field K] [NumberField K] [IsCyclotomicExtension {N} ℚ K],
    ERH.ExtendedRiemannHypothesis K
```

## Tier and provenance

| Theorem | Tier | Hypothesis |
|---|---|---|
| `AbelianERH.abelianERH_of_GRH` | C + H | `DirichletLZerosOnLine` (GRH, RH-type) and `KroneckerWeberStatement` (a known theorem) |
| `AbelianERH.extendedRiemannHypothesis_of_algHom` | C | `DirichletLZerosOnLine` |
| `AbelianERH.subfield_extendedRiemannHypothesis_of_GRH` | C | `DirichletLZerosOnLine` |
| `AbelianERH.cyclotomicERH_of_GRH` | C | `DirichletLZerosOnLine` |
| `AbelianERH.cyclotomic_extendedRiemannHypothesis_of_GRH` | C | `DirichletLZerosOnLine` |
| `AbelianERH.extendedRiemannHypothesis_of_coeff` | C | `DirichletLZerosOnLine`, plus a coefficient identity proved per field |
| `AbelianERH.Unconditional.abelianERH` (`Unconditional/`) | U | none; GRH (`LFunction_eq_zero_re`) and Kronecker–Weber (`kwHom`) from riemann-hypothesis |
| `AbelianERH.Unconditional.cyclotomicERH` (`Unconditional/`) | U | none; GRH from riemann-hypothesis |
| `AbelianERH.Unconditional.kroneckerWeber` (`Unconditional/`) | U₀ | none; riemann-hypothesis's class field theory, no RH or GRH |
| `AbelianERH.Unconditional.isDedekindZeta_continuedDedekindZeta` (`Unconditional/`) | U₀ | none; riemann-hypothesis's Tate-thesis continuation, no RH or GRH |

* `ERH.IsDedekindZeta` and `ERH.ExtendedRiemannHypothesis` are copied word for word from
  google-deepmind/formal-conjectures,
  [`FormalConjectures/Millennium/RiemannHypothesis.lean`](https://github.com/google-deepmind/formal-conjectures/blob/9097e2f90e66d2f6244209cb1c07f7120d17ec53/FormalConjectures/Millennium/RiemannHypothesis.lean)
  (commit `9097e2f9`, Apache-2.0). There `ERH.extended_riemann_hypothesis` (all number fields) is
  `research open`; formal-conjectures has no abelian or cyclotomic version, so
  `CyclotomicERHStatement` and `AbelianERHStatement` are this repository's own. The same
  predicate is `ArtinPrimitiveRootsConjecture.DedekindZetaRH` in
  `FormalConjectures/Wikipedia/ArtinPrimitiveRootsConjecture.lean`.
* `DirichletLZerosOnLine` (the only RH-type hypothesis) is copied word for word from
  leanprover-community/riemann-hypothesis `src/Statements.lean` at `507a75d91d`. It is GRH for
  every Dirichlet L-function, imprimitive characters included, in the critical strip.
* `KroneckerWeberStatement` (a known theorem: Kronecker 1853, Weber 1886, Hilbert 1896) is the type
  of riemann-hypothesis's `UpperTheory.V.CF.kwHom`. It is not in Mathlib at this pin (Mathlib PR
  #46376 is open), so the main library takes it as a hypothesis (tier H) and `Unconditional/`
  discharges it with `kwHom`.
* `ERH.ExtendedRiemannHypothesis K` quantifies over all continuations `Z`, so it would hold
  vacuously if `ζ_K` had none. `isDedekindZeta_continuedDedekindZeta` rules that out: the
  Tate-thesis continuation of riemann-hypothesis is an `IsDedekindZeta K`, for every number field.

## Axioms

Main library, `lake env lean` on a file importing `AbelianERH`:

```
'AbelianERH.cyclotomicERH_of_GRH' depends on axioms: [propext, Classical.choice, Quot.sound]
'AbelianERH.cyclotomic_extendedRiemannHypothesis_of_GRH' depends on axioms: [propext, Classical.choice, Quot.sound]
'AbelianERH.extendedRiemannHypothesis_of_coeff' depends on axioms: [propext, Classical.choice, Quot.sound]
'AbelianERH.dedekindZeta_eq_mul_prod' depends on axioms: [propext, Classical.choice, Quot.sound]
'AbelianERH.LSeries_eq_exp_logLCoeff' depends on axioms: [propext, Classical.choice, Quot.sound]
'AbelianERH.coeffIdentity_cyclotomic' depends on axioms: [propext, Classical.choice, Quot.sound]
'AbelianERH.abelianERH_of_GRH' depends on axioms: [propext, Classical.choice, Quot.sound]
'AbelianERH.extendedRiemannHypothesis_of_algHom' depends on axioms: [propext, Classical.choice, Quot.sound]
'AbelianERH.subfield_extendedRiemannHypothesis_of_GRH' depends on axioms: [propext, Classical.choice, Quot.sound]
'AbelianERH.coeffIdentity_subfield' depends on axioms: [propext, Classical.choice, Quot.sound]
'AbelianERH.dedekindZeta_congr' depends on axioms: [propext, Classical.choice, Quot.sound]
```

The proof uses no `native_decide` and no finite computation, and the repository has no `sorry`.

## Proof outline

1. `AbelianERH/DirichletExp.lean`: `L(s, χ) = exp(∑ χ(n) Λ(n)/log n · n^{-s})` for `Re s > 1`
   (`LSeries_eq_exp_logLCoeff`): both sides have logarithmic derivative `-L(χΛ, s)` (Mathlib's
   `LSeries_twist_vonMangoldt_eq`) on the connected half-plane and tend to `1` as `s → +∞`.
2. `AbelianERH/Factorisation.lean`, `vonMangoldtK_prime_pow`: if every prime of `K` above `q`
   has inertia degree `f` and `#{𝔮 ∣ q} · f = [K:ℚ]`, then `Λ_K(q^k) = [K:ℚ] log q · [f ∣ k]`.
   `Λ_K` is artin-grh's `vonMangoldtK`, the coefficients of `-ζ_K'/ζ_K`.
3. Same file, `dedekindZeta_eq_mul_prod`: given `Λ_K(n) = ∑_{χ ∈ X} χ(n) Λ(n)` for `(n, N) = 1`,
   `ζ_K(s) = E(s) ∏_{χ ∈ X} L(s, χ)` for `Re s > 1`, where `E = exp(∑_{(n,N)>1} Λ_K(n)/log n ·
   n^{-s})`. This compares the logarithms: artin-grh's `dedekindZeta_eq_exp` gives
   `ζ_K = exp(∑ Λ_K(n)/log n · n^{-s})`, and `χ(n) = 0` when `(n, N) > 1`.
4. `E` is holomorphic and zero-free on `Re s > 0`: the exponent is supported on `p^k` with
   `p ∣ N`, with coefficients at most `[K:ℚ]`, so its abscissa of absolute convergence is `≤ 0`
   (`abscissaOfAbsConv_ramCoeff_le`).
5. `extendedRiemannHypothesis_of_coeff`: `{Re s > 0} ∖ {1}` is connected (a union of four convex
   pieces), so any `Z` with `IsDedekindZeta K Z` equals `E · ∏ L(·, χ)` there (identity theorem).
   A zero of `Z` in the strip is a zero of some `L(s, χ)`, and `DirichletLZerosOnLine` applies.
   No functional equation is needed.
6. `AbelianERH/Cyclotomic.lean`: for `K = ℚ(ζ_N)` and `q ∤ N`, Mathlib gives `e = 1` and
   `f = ord_N(q)` (`IsCyclotomicExtension.Rat.inertiaDeg_eq_of_not_dvd`,
   `ramificationIdxIn_eq_of_not_dvd`), and the fundamental identity gives `#{𝔮 ∣ q} · f = φ(N)`.
   Orthogonality (`DirichletCharacter.sum_characters_eq`) gives
   `∑_χ χ(q^k) = φ(N) · [q^k ≡ 1 mod N] = φ(N) · [f ∣ k]`. So step 3 applies with all characters
   mod `N` (`coeffIdentity_cyclotomic`).
7. `AbelianERH/Subfield.lean`: for an intermediate field `F` of `L = ℚ(ζ_N)`, with
   `H = Gal(L/F)` and `H_N ≤ (ℤ/N)ˣ` its image, take `X(F)` = the characters trivial on `H_N`
   (Mathlib's `intermediateFieldEquivSubgroupChar`, `#X(F) = [F:ℚ]`). Orthogonality on `G/H_N`
   gives `∑_{χ ∈ X(F)} χ(a) = [F:ℚ]·[a ∈ H_N]` (`sum_charsOf`). For `q ∤ N` (`subfield_split`):
   the tower `ℚ ⊆ F ⊆ L` (Mathlib's `ramificationIdxIn_mul_ramificationIdxIn`,
   `inertiaDegIn_mul_inertiaDegIn`) gives `e_F = 1` and `f_F · f(𝔔/𝔮) = ord_N(q)`, and
   `f(𝔔/𝔮) = #Stab_H(𝔔) = #(H_N ∩ ⟨q⟩)` (`card_stabilizer_eq`, `galEquivZMod_stabilizer`).
   Then `q^k ∈ H_N ⟺ f_F ∣ k` (`pow_mem_iff_dvd`, the kernel of `⟨q⟩ → G/H_N`), so the
   coefficient identity holds with `X(F)` (`coeffIdentity_subfield`).
8. Same file: `ζ_K` is invariant under `K ≃+* K'` (`dedekindZeta_congr`: ideals correspond with
   isomorphic quotients), so ERH passes from `φ(K) ⊆ ℚ(ζ_N)` to `K`
   (`extendedRiemannHypothesis_of_algHom`), and Kronecker–Weber supplies `φ` for abelian `K`
   (`abelianERH_of_GRH`).

This is the scoping report's "route C" (`docs/scoping/abelian-erh.md` in the conjectures
workspace). It uses imprimitive characters, so ramified primes never need an exact Euler factor:
they all go into `E`.

## Layout

| File | Content |
|---|---|
| `AbelianERH/Statement.lean` | fixed targets and hypotheses (copied definitions) |
| `AbelianERH/DirichletExp.lean` | `L(s, χ) = exp(∑ χΛ/log · n^{-s})` on `Re s > 1` |
| `AbelianERH/Factorisation.lean` | `Λ_K` at unramified prime powers; `ζ_K = E ∏ L`; ERH from a coefficient identity |
| `AbelianERH/Cyclotomic.lean` | the coefficient identity for `ℚ(ζ_N)` |
| `AbelianERH/Subfield.lean` | subfields of `ℚ(ζ_N)`, transport along `≃+*`, the abelian headline |
| `Unconditional/AbelianERHUnconditional.lean` | GRH and Kronecker–Weber from riemann-hypothesis |
| `scripts/check-unconditional.sh` | links and checks `Unconditional/` |

## Deviations from the literature

* Kronecker–Weber is a hypothesis of the main library (Mathlib lacks it at this pin), discharged
  only in `Unconditional/`.
* We prove ERH, not the exact factorisation `ζ_K = ∏ L(s, χ*)` over primitive characters: our
  `ζ_K = E · ∏_{χ mod N} L(s, χ)` uses imprimitive characters and an explicit zero-free factor
  `E`, which is all that ERH needs.
* The hypothesis is riemann-hypothesis's `DirichletLZerosOnLine` (all characters), not
  formal-conjectures' `GRH.generalized_riemann_hypothesis` (primitive characters, trivial zeros
  excluded). The two differ by the Euler factors `1 − χ*(p)p^{-s}`, whose zeros lie on
  `Re s = 0`; the bridge is not formalised here.

## What remains

Nothing on the path to `AbelianERHStatement` is open: the main library proves it from GRH and
Kronecker–Weber, and `Unconditional/` supplies both from riemann-hypothesis. To make the main
library free of the `KroneckerWeberStatement` hypothesis, bump to a Mathlib pin that contains
Kronecker–Weber (PR #46376) and discharge it there. GRH itself is the only RH-type input, and
ERH for abelian fields is equivalent to it.

## Building

Lean `v4.36.0`, Mathlib `fc4f59e5` (through erdos-985). Requires erdos-985 at `9538edb` and
artin-grh at `5263600` (for `vonMangoldtK` and `dedekindZeta_eq_exp`; only
`Artin.Analytic.Core.VonMangoldt` and its imports are built).

```
lake exe cache get
lake build
```

The four proof modules take well under a minute of CPU together; building the artin-grh modules
they import takes about a minute.

## Unconditional version

| Theorem | Statement | Axioms |
|---|---|---|
| `AbelianERH.Unconditional.abelianERH` | `AbelianERHStatement` | `propext, Classical.choice, Quot.sound` |
| `AbelianERH.Unconditional.abelian_continuedDedekindZeta_zero` | zeros of the Tate-thesis continuation of `ζ_K`, `K` abelian, in the strip have `Re s = 1/2` | `propext, Classical.choice, Quot.sound` |
| `AbelianERH.Unconditional.cyclotomicERH` | `CyclotomicERHStatement` | `propext, Classical.choice, Quot.sound` |
| `AbelianERH.Unconditional.cyclotomic_continuedDedekindZeta_zero` | the same for `ℚ(ζ_N)` | `propext, Classical.choice, Quot.sound` |
| `AbelianERH.Unconditional.kroneckerWeber` (U₀) | `KroneckerWeberStatement` | `propext, Classical.choice, Quot.sound` |
| `AbelianERH.Unconditional.isDedekindZeta_continuedDedekindZeta` (U₀) | `ERH.IsDedekindZeta K (GroundTheory.Global.continuedDedekindZeta K)` | `propext, Classical.choice, Quot.sound` |

Output of `scripts/check-unconditional.sh` on 2026-11-24 (riemann-hypothesis `507a75d91d`, 24 min
wall on a loaded box, no `sorryAx`):

```
'AbelianERH.Unconditional.kroneckerWeber' depends on axioms: [propext, Classical.choice, Quot.sound]
'AbelianERH.Unconditional.abelianERH' depends on axioms: [propext, Classical.choice, Quot.sound]
'AbelianERH.Unconditional.abelian_continuedDedekindZeta_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'AbelianERH.Unconditional.cyclotomicERH' depends on axioms: [propext, Classical.choice, Quot.sound]
'AbelianERH.Unconditional.isDedekindZeta_continuedDedekindZeta' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'AbelianERH.Unconditional.cyclotomic_continuedDedekindZeta_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

`abelianERH` is ERH for every finite abelian extension of `ℚ`, with no hypothesis left. ERH for
abelian fields is equivalent to GRH for Dirichlet L-functions, so this theorem is GRH in another
form. `Unconditional/AbelianERHUnconditional.lean` imports, at commit `507a75d91d`,
riemann-hypothesis's `Main` (`LFunction_eq_zero_re : DirichletLZerosOnLine`, the GRH claim), the
module of `UpperTheory.V.CF.kwHom` (Kronecker–Weber, a known theorem; no RH involved) and the
Tate-thesis module `GroundTheory.GlobalFields.TateThesis.DedekindZetaContinuation` (a
continuation of `ζ_K`, used only to show the statement is not vacuous). Check it with

```
scripts/check-unconditional.sh /path/to/riemann-hypothesis
```

It needs the riemann-hypothesis cache (about 93 GB), about 19 GB of RAM and roughly 900k open
files (`ulimit -n`; on Linux, `sudo prlimit --pid $$ --nofile=2000000:2000000`).

*The riemann-hypothesis proof adds no axioms of its own. It was certified by the Lean FRO and the Mathlib Initiative on 2026-11-21, and independent kernels accept it (math.mit.edu/~drew/grh). This check links against the community build cache and does not repeat those kernel checks.*

## Credits and prior work

* artin-grh (`github.com/senamakel/artin-grh`, commit `5263600`) is a lake dependency, not
  vendored: `Artin.Analytic.vonMangoldtK`, `dedekindZeta_eq_exp` and the splitting helpers.
  `LSeries_eq_exp_logLCoeff` follows its proof of `dedekindZeta_eq_exp`.
* The definitions in `AbelianERH/Statement.lean` are copied from formal-conjectures (Apache-2.0,
  commit `9097e2f9`) and riemann-hypothesis (`507a75d91d`, statement definitions only; nothing
  else is copied from that repository, which has no licence).
* Prior Lean work: TauCeti (`TauCetiProject/TauCeti`, Apache-2.0) proves the exact factorisation
  `ζ_K = ∏ L(s, χ*)` for cyclotomic and quadratic fields on another Lean/Mathlib pin. Nothing is
  copied from it; this repository proves its own (weaker, `E`-twisted) factorisation by a
  different route. As far as a search of Mathlib, formal-conjectures and GitHub code search
  (`dedekindZeta`, `ExtendedRiemannHypothesis`, `DedekindERH`, 2026-11-24) found, no earlier Lean
  development derives zeros-on-the-line for `ζ_K` of a field other than `ℚ` from GRH.
