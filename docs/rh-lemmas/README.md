# What riemann-hypothesis proves on the way to RH

An inventory, taken 2026-11-24, of the intermediate lemmas in
[riemann-hypothesis](https://github.com/leanprover-community/riemann-hypothesis) at commit
`507a75d91d` (about 149,000 Lean files, 15 million lines, no comments). Until now this workspace
imported only its two final theorems. These files record what else is in there that we could
import.

## How far to trust this

- **Read, not built.** Nine agents read statements and the definitions behind them. Nobody ran
  `lake`, `lean` or `#print axioms`. "Proved" means a hypothesis-free theorem of that type exists
  in the source and a text search finds no `sorry`, `axiom`, `opaque` or `native_decide`.
- **Names are not evidence.** `WeilBound` has no Weil bound, `PositivityTheory` no positivity,
  `DedekindLFunctions` no Dedekind zeta, `SemistableReduction` no curves, and `Heights` no
  Northcott or Mordell–Weil. `PublishedTheorems/` states about 391 classical theorems as `Prop`s,
  and about 170 of them have no proof anywhere in the repo.
- **The RH-strength step is unaudited.** The final contradiction rests on internal definitions
  (`VWin`, `Row0b`, bounds on Tate–Shafarevich lengths, the `D7` bundle) that no agent checked
  for faithfulness. One statement, `principalPolarisationOneSection`, looks false as named.
- **Same trust caveat as the final theorems.** Anything imported from here inherits it: the
  cache holds outputs of untrusted builds, and the proof has not been independently verified.
- **No licence.** We may import the repo as a dependency. We may not copy its code. These files
  paraphrase statements and give names and paths only.

Two corrections to the reports, found afterwards. riemann-hypothesis is on Lean `v4.36.0`
(its README's `v4.33.1` is out of date), the same toolchain as this workspace, so the toolchain
caveat in `targets-algebraic.md` does not apply. And the strip bound that report lists as
missing for `DedekindContinuation` was proved in artin-grh PR #11, now merged. Global
Kronecker–Weber exists (`UpperTheory.V.CF.kw`, file 03), although file 07 says it does not.

Before any of these lemmas goes on the path to a headline theorem, open its statement, check the
definitions it uses, and run `#print axioms` on it.

## Files

| File | Subtree | Files covered |
|---|---|---:|
| [00-proof-spine.md](00-proof-spine.md) | `Main.lean` backwards, zero-free regions, the analytic core | spine |
| [01-abelian-variety-statements.md](01-abelian-variety-statements.md) | `Development/AbelianVarietyTheory` except `Proofs/` | 2,951 |
| [02-abelian-variety-proofs.md](02-abelian-variety-proofs.md) | `Development/AbelianVarietyTheory/Proofs` | 78,548 |
| [03-automorphic-arithmetic.md](03-automorphic-arithmetic.md) | `Development/AutomorphicArithmetic` | 17,522 |
| [04-automorphic-spectrum.md](04-automorphic-spectrum.md) | `Development/AutomorphicSpectrum`, `DiscreteGroups` | 13,769 |
| [05-weil-etale-resolution.md](05-weil-etale-resolution.md) | `Development/WeilBound`, `EtaleCohomology`, `ResolutionOfSingularities` | 8,604 |
| [06-formalism.md](06-formalism.md) | `Formalism` | 15,292 |
| [07-ground-theory.md](07-ground-theory.md) | `GroundTheory` | 6,667 |
| [08-reciprocity-companion-positivity-lemmata.md](08-reciprocity-companion-positivity-lemmata.md) | `ReciprocityTheory`, `CompanionTheory`, `PositivityTheory`, `Lemmata`, `Supplements` | 6,040 |

The matching of these lemmas to targets is in three further reports:
[targets-analytic.md](targets-analytic.md), [targets-algebraic.md](targets-algebraic.md) and
[targets-geometry-algebra.md](targets-geometry-algebra.md).

Each inventory file has the same sections: scope and method, what the subtree really is, the inventory
table (declaration, `path:line`, paraphrased statement, reusability), internal definitions,
mechanical families, standalone value, and what was not verified.

## The reusable results, by topic

Declaration names and paths are in the file given in brackets.

### Primes and Dirichlet L-functions, with no hypothesis

- Zero-free region for ζ and the prime number theorem with error `x·exp(−c√log x)` [00].
- Zero-free region for Dirichlet L-functions with at most one exceptional zero, Landau–Page,
  Siegel's theorem and Siegel–Walfisz [00, 01].
- Prime number theorem in progressions with the exceptional-zero term (Gallagher). One copy is
  proved only for moduli divisible by 8 [02, 06].
- Deuring–Heilbronn repulsion, a log-free zero-density bound, the multiplicative and hybrid
  large sieve, Brun–Titchmarsh, Turán's power-sum theorem [02, 06].
- Linnik's theorem, with no explicit exponent [01, 03].
- A truncated Perron formula, a contour-shift and residue identity, zero counts in unit
  windows, and the approximation of `L′/L` by nearby zeros [00].
- A windowed Landau theorem: a one-sided bound on weighted prime sums over late windows gives a
  zero-free half-plane [00, 03].
- Landau's theorem for Dirichlet series with nonnegative coefficients [03, 05].
- Explicit elementary bounds: `π(y) < 1.26·y/log y` for `y > 1`, Chebyshev, Mertens [04, 06].

### Number fields and class field theory

- Global class field theory for every number field: the Artin map and its kernel, the existence
  theorem, and `ClassGroup (𝓞 K) ≃* Gal(H/K)` sending primes to Frobenius [07].
- Chebotarev, in Dirichlet-density form [07] and in existence form [01, 02, 04].
- Meromorphic continuation, functional equation and residue of Mathlib's `dedekindZeta`; the
  same for Hecke L-functions, with nonvanishing on `Re s ≥ 1` [01, 04, 07].
- Local class field theory, local and global Kronecker–Weber, local Tate duality, Tate's Euler
  characteristic formula, `Br(K) ≅ ℚ/ℤ`, the Hasse norm theorem for cyclic extensions [03, 07, 08].
- Imaginary quadratic fields: `ζ_K = ζ·L(χ)`, `L(1,χ) = πh/√d`, the Kronecker limit formula,
  Chowla–Selberg [02].
- Complex multiplication: the main theorem with `K(j) = H_K`, and integrality of singular
  moduli [07, 08].
- Stickelberger for cyclotomic fields, Ferrero–Washington in bounded-rank form,
  `L(1−k, χ) = −B_{k,χ}/k`, Deligne–Ribet for totally real fields [03, 05].
- Class-number upper bounds for every number field, and Minkowski's theorem that every
  nontrivial extension of ℚ ramifies [03, 06].

### Geometry, algebra and analysis

- Hironaka's resolution of singularities and principalisation in characteristic 0, in functorial
  form, on Mathlib schemes [05].
- Hörmander's L² estimate, Skoda division and Osgood's lemma [08].
- Brouwer's fixed point theorem and invariance of domain in `ℝⁿ` [07].
- Étale cohomology with the Gysin sequence. Poincaré duality and the Frobenius-weight statement
  are stated and not proved [05].
- Finiteness of coherent cohomology for proper schemes; regular local rings are domains, UFDs
  and Cohen–Macaulay [07, 08].
- Abelian schemes: `#A[n] = n^{2g}`, the Weil pairing, the cube theorem, on bespoke definitions [02].
- Brauer–Nesbitt, Burnside, Jordan's prime-cycle theorem, Skolem–Noether, Witt's extension
  theorem for Hermitian forms [06, 07].
- The upper half of Minkowski's second theorem and Harder–Narasimhan filtrations for
  lattices [06].

## What is not there

- No Weil bound, Kloosterman sums or point counts for curves over finite fields.
- No proof of the explicit formulae `ExplZeta` / `ExplChi`, Jutila's zero-density theorem,
  Page's theorem, local Langlands for `GL_n` or general Poitou–Tate. All are stated only.
- No zeros of `ζ_K` beyond the functional equation and the pole, so nothing towards GRH for
  non-abelian fields.
- No Hadamard factorisation, digamma estimates or `1/(s(s+1))` kernel (unchanged from the
  2026-11-22 audit; erdos-985 supplies these).

The conjectures these lemmas open up are ranked in [`../NEXT_TARGETS.md`](../NEXT_TARGETS.md).
