# Targets for the non-arithmetic lemmas of riemann-hypothesis

Research pass, 2026-11-24. This covers only the slice outside analytic and algebraic number theory. Nothing was
built and no repo was edited. Sources read: `docs/rh-lemmas/05`, `06`, `07`, `08` and `01` in full, a grep of
the other four, the Mathlib sources at `fc4f59e5`, all 2,196 rows of the Conjecture Atlas, the formal-conjectures
tree on GitHub (`main`, 2,478 paths; about 30 files read), and the riemann-hypothesis sources at `507a75d91d`.

## Summary

This slice gives **few real targets**. Every strong match is algebraic geometry or commutative algebra, and comes
from the resolution-of-singularities and regular-local-ring lemmas. Brouwer, invariance of domain, Hörmander,
Osgood, Markov, Lie–Trotter, Minkowski II, Harder–Narasimhan, Brauer–Nesbitt, Skolem–Noether, Witt, Jordan,
Casselman–Shalika and the local converse theorem match **no** open Atlas row or unproved formal-conjectures
statement in which they are the missing ingredient. Two caveats apply to everything below:

- **None of these is a consequence of RH.** The AGENTS.md tier table has no row for "imports riemann-hypothesis
  for a non-RH lemma". I write **U-imp** for that case. It carries the same trust caveat as tier U (an untrusted
  cache and an unlicensed source) but discharges no RH or GRH hypothesis. Whether this workspace should take such
  targets at all is the user's decision.
- **There is a better source for Hironaka.** [resolutionorg/hironaka](https://github.com/resolutionorg/hironaka)
  is an Apache-2.0 Lean 4 library on Mathlib (Lean v4.35.0, created 2026-09-30). It proves Hironaka's Main
  Theorem I in Mathlib's own language (`AlgebraicGeometry.exists_isBlowUpAlong_smooth`), plus Kollár's
  functorial resolution and principalisation. Its README says the library has no `sorry`, is checked by
  comparator, and uses only the standard three axioms. I have not checked those claims myself. For targets 1
  and 2 it beats the unlicensed riemann-hypothesis repo: it is licensed, it does not need the 93 GB import, and
  the result would be **tier D** under the current rules. riemann-hypothesis stays a fallback.

## Mathlib check (task 1)

These results are in Mathlib at `fc4f59e5` and were dropped:

| Result | Mathlib at `fc4f59e5` |
|---|---|
| Jordan's theorem, swap and 3-cycle forms | Has both (`GroupTheory/GroupAction/Jordan.lean`: `subgroup_eq_top_of_isPreprimitive_of_isSwap_mem`, `alternatingGroup_le_of_isPreprimitive_of_isThreeCycle_mem`). Only the riemann-hypothesis **p-cycle** form (n ≥ p+3) is new. |
| Burnside's density theorem | Follows from the algebraically-closed Wedderburn–Artin theorem (`RingTheory/SimpleModule/IsAlgClosed.lean`) plus Schur. Treated as present. |
| Poisson summation, 1-D and Gaussian | Has it (`Analysis/Fourier/PoissonSummation.lean`, `Gaussian/PoissonSummation.lean`). Only the riemann-hypothesis n-dimensional complex-symmetric Gaussian form is new. |
| Generic smoothness | Has it (`Scheme.Hom.dense_smoothLocus_of_perfectField`). It is needed in target 1. |
| Birational maps, valuative criterion | Has them (`Scheme.BirationalOver`, `ValuativeCriterion`, `IsProper.eq_valuativeCriterion`). Both are needed in targets 1 and 2. |

These are **absent** from Mathlib, so the riemann-hypothesis version would be new: blowups of schemes; Hironaka
and principalisation; regular ⇒ domain / UFD / Cohen–Macaulay; Serre's finite projective dimension over regular
local rings; smooth ⇒ regular stalks; finiteness of coherent cohomology; étale cohomology and Gysin; Kawamata–Viehweg
and Nadel vanishing; Hörmander, Skoda and multivariable Osgood; Brouwer and invariance of domain; Markov brothers;
Lie–Trotter; Minkowski II and Harder–Narasimhan; Brauer–Nesbitt and Skolem–Noether; Hermitian Witt extension;
#E[n] = n² and #A[n] = n^{2g}; Casselman–Shalika; the local converse theorem.

## Ranked targets

| # | Target | Source + Atlas id / formal-conjectures file | RH-repo lemmas used (decl name, path) | Already in Mathlib? | What is still missing | Expected tier | Effort |
|---|---|---|---|---|---|---|---|
| 1 | Hironaka: an integral, separated, finite-type scheme over a char-0 field has a resolution (integral Y, smooth over k, Y → X proper and birational) | Hironaka, Ann. Math. 79 (1964). Atlas `wiki-resolution-of-singularities` (row is "open" because of char p). fc `Wikipedia/ResolutionOfSingularities.lean`, `resolution_of_singularities_of_charZero` (research solved, `sorry`) | `FunctorialResolution.functorialResolutionCharZero` (`Development/ResolutionOfSingularities/HasSimpleNormalCrossingsOfInStrictNormalCrossing.lean:19`); `isReduced_of_smooth` (`…/EmbeddedResolution/EtaleCoordinates/SmoothRegular.lean:256`) | No (it has generic smoothness, `BirationalOver` and `IsProper`) | Glue only. Get Y integral from: Y is reduced (smooth), it has a dense open isomorphic to the irreducible smooth locus of X, so it is irreducible. Build the `PartialIso` from the iso over `f.smoothLocus`. Or use hironaka's `exists_isBlowUpAlong_smooth` and do the same glue | U-imp (riemann-hypothesis) or **D** (hironaka) | S |
| 2 | Zariski's local uniformisation in char 0 | Zariski, Ann. Math. 41 (1940) 852–896 (confirmed). No Atlas row. fc `Wikipedia/LocalUniformization.lean`, `local_uniformization_of_charZero` (research solved, `sorry`) | as #1, plus `isRegularLocalRing_stalk_of_smooth` (`SmoothRegular.lean:228`) | No (it has the valuative criterion) | Pick an affine model B = k[y₁..yₙ] ⊆ 𝒪 with yᵢ = xᵢ or xᵢ⁻¹. Resolve Spec B. Lift Spec 𝒪 through the proper resolution map by the valuative criterion. Take an affine chart A at the centre; its stalk is regular. Extra work: the universe change (fc has k and F in independent universes; riemann-hypothesis needs `Scheme.{u}` with k : Type u) and identifying Γ(U) with a subalgebra of F | U-imp or **D** (hironaka) | M |
| 3 | Auslander–Reiten over a regular local ring: Extⁱ(M,R) = 0 for all i > 0 ⇒ M free | Textbook (stated as such in fc). No Atlas row. fc `Paper/AuslanderReiten.lean`, `auslander_reiten.variants.regular_local` (textbook, `sorry`) | `GroundTheory.Arith.SchemeCoh.hasProjectiveDimensionLT_of_isRegularLocalRing` (`GroundTheory/ArithmeticGeometry/SchemeCohomology/RegularUFDSerre.lean:197`), Serre's theorem | No. Mathlib has `HasProjectiveDimensionLT` and the Ext long exact sequences, but not Serre's theorem | Dimension-shifting induction on projective dimension: syzygy K is free by induction; Ext¹(M,K) ≅ Ext¹(M,R)ⁿ = 0, so 0→K→F→M→0 splits; projective over local ⇒ free | U-imp (or D if Serre's theorem is re-proved, about +M) | S–M |
| 4 | Briançon–Skoda: for I ⊆ 𝒪ₙ (or ℂ[z]) with m generators, the integral closure of I^{min(m,n)+l−1} lies in I^l | Briançon–Skoda, C. R. Acad. Sci. 278 (1974); the case m ≤ n comes directly from Skoda's L² division (confirmed: Sznajdman arXiv:0807.0142, Andersson MMJ 2006). No Atlas row. **No fc statement** | `ReciprocityTheory.L2DbarEstimates.skoda` (`ReciprocityTheory/L2DbarEstimates/NormFibrations/Hormander.lean:37`), `hormander` (:31), `EtaleStein` (`…/IsLocalHomeomorph.lean:118`) | No (Mathlib has no ring 𝒪ₙ of convergent germs and no several-complex-variables L² theory) | A germ ring or polynomial-ring statement. A Stein ball with a smooth psh exhaustion. Integral closure gives \|φ\| ≤ C\|f\|^N. Skoda needs p ≥ 2 and t > p−1, so the cases m = 1 and m > n (reduction of ideals) need separate arguments. For ℂ[z], descent from germs by faithful flatness of completion | U-imp | XL |
| 5 | Serre's dimension inequality dim M + dim N ≤ dim R (regular local R, finite-length M ⊗ N) | Serre, *Local Algebra* V.B. Atlas `wiki-serre-s-multiplicity-conjectures` (partially resolved). fc `Wikipedia/SerreMultiplicityConjectures.lean`, `supportDim_add_supportDim_le_ringKrullDim` (research solved, `sorry`) | `hasProjectiveDimensionLT_of_isRegularLocalRing` (as #3); `ReciprocityTheory.CA.isCM_of_isRegularLocalRing` (`ReciprocityTheory/CommutativeAlgebra/CohenMacaulay/IsCMOfIsRegularLocalRing.lean:12`); `IsRegularLocalRing.isDomain` (`…/CohenMacaulay/RegGensA.lean:382`); `height_add_ringKrullDim_quotient_mvPolynomial_field` | No | Reduction to the diagonal. That needs the Cohen structure theorem and the completion of regular local rings, which is not in Mathlib and not in riemann-hypothesis as far as the inventories show. The lemmas only make χ well defined (Tor vanishes above dim R) | U-imp | XL |
| 6 | Small Cohen–Macaulay modules in dimension ≤ 2 | Hochster. Atlas `wiki-homological-conjectures-in-commutative-algebra`. fc `Wikipedia/SmallCohenMacaulayModules.lean`, `exists_isSmallCohenMacaulay.variants.ringKrullDim_le_two` | `IsCM`, `IsCM.localization_atPrime` (`…/CohenMacaulay/LocDim.lean:59`), `IsCMMod.associatedPrimes_eq_minimalPrimes` (`Unmixed.lean:114`) | No | Finiteness of the normalisation of a complete local domain (Nagata), Serre's S₂ criterion for normal rings, S₂ in dimension 2 ⇒ CM. The riemann-hypothesis CM lemmas are a minor input | U-imp | L |
| 7 | Fujita-type effective global generation (Angehrn–Siu) | Atlas `wiki-fujita-conjecture` (open; Angehrn–Siu 1995 gives the quadratic bound, *(unverified here)*). No fc statement | `GlobalTheory.Published.PointSeparationPair` → `pointSeparationPair` (`Development/WeilBound/CoreStatements/AutomorphicKernels/NadelVanishing/TopPointSep.lean:10`); `exists_sec_sep_of_lcCut`; `kawamataViehweg_of_nadelVanishingPair` (`Development/AbelianVarietyTheory/Proofs/DivisorProofs/KawamataViehwegOfNadelVanishingPair.lean:66`) | No | The concentration-of-multiplier-ideals construction. Also, everything is stated with internal `LB`, `coh`, `CanonLB` and `KltAt` on `Scheme.{0}` over ℂ, so a Mathlib-level statement needs a bridge | U-imp | XL |

## Top five in detail

**1. Hironaka (fc `resolution_of_singularities_of_charZero`).** I opened `Statements.lean`. `IsResolutionRuleCharZero`
takes any field k : Type u of characteristic 0 and any X : `Scheme.{u}` that is reduced, quasi-compact and locally
of finite type over Spec k. It returns a finite blowup tower whose top is smooth over k and proper over X, is an
isomorphism over `f.smoothLocus`, and has dense preimage of that locus, with an SNC exceptional locus. Separatedness
is not required. The fc hypotheses (integral, separated, finite type, same universe u) are stronger, so the match
is exact. `IsBlowup` is the universal property, built from Mathlib's `IdealSheafData.comap`. Three steps are left.
(a) Y is reduced, by `isReduced_of_smooth`. (b) Y is irreducible, because the preimage of the smooth locus is dense
and isomorphic to an open of the irreducible X. (c) The two opens form a Mathlib `PartialIso` over the identity of X.
Then `isIntegral_of_irreducibleSpace_of_isReduced` closes it. This is the cheapest real result in the slice: a
`research solved` formal-conjectures statement. The same glue on top of resolutionorg/hironaka gives tier D with no
93 GB import.

**2. Local uniformisation (fc `local_uniformization_of_charZero`).** This uses the same rule as #1, applied to an
affine model inside 𝒪, so no projective closure is needed: properness of the resolution map is enough for the
valuative criterion. I checked `isRegularLocalRing_stalk_of_smooth`. It takes any field k : Type u, any
X : `Scheme.{u}` smooth over Spec k and any point, and returns Mathlib's `IsRegularLocalRing` for the stalk. That
is the regularity the fc predicate `HasLocalUniformization` asks for (A localised at the centre is regular), once
A_𝔭 is identified with the stalk. The main friction is universes and the embedding of Γ(U) into F. Zariski 1940 is
confirmed as the source (Ann. Math. 41, 852–896).

**3. Auslander–Reiten, regular local case.** I opened `RegularUFDSerre.lean`. `hasProjectiveDimensionLT_of_isRegularLocalRing`
takes R : Type u with Mathlib's `IsRegularLocalRing`, a proof that `ringKrullDim R = d`, and any finite module
M : Type u. It returns Mathlib's `HasProjectiveDimensionLT (ModuleCat.of R M) (d+1)`. The fc statement has R and M
in the same universe u, so it fits. The rest is about 100 lines of Ext bookkeeping on Mathlib's
`Abelian.Ext`. It is labelled textbook, so it is not a headline result. But it is a clean, short first use of the
commutative-algebra layer, and Serre's theorem itself would be worth upstreaming.

**4. Briançon–Skoda.** I opened `JacobianInterpolationStatement.lean`. `SStatement n M` holds for every `EtaleStein n M`:
a local homeomorphism to ℂⁿ with a smooth psh exhaustion that has compact sublevels. It takes p ≥ 2 holomorphic gᵢ
with no common zero (on M itself, so one works on the complement of the zero set), a smooth psh weight with Levi
form ≥ 0, t > p−1, and holomorphic f with finite weighted L² norm. It returns holomorphic hᵢ with f = Σgᵢhᵢ and
Skoda's bound t/(t−(p−1)). That is Skoda's theorem in the generality Briançon–Skoda needs for 2 ≤ m ≤ n, applied
on a ball minus V(I) and extended over V(I) with `L2DbarEstimates.ext` (L² Riemann extension, `MvBlowup.lean:13`).
The cases m = 1 and m > n need extra arguments. There is no formal statement to copy, so one would have to be
written (rule 3), and Mathlib lacks a convergent-germ ring. This is the only real Hörmander-side target, and it
is XL.

**5. Serre's dimension inequality.** The riemann-hypothesis lemmas (finite projective dimension, regular ⇒ CM ⇒
domain, dimension formula in polynomial rings) are genuine inputs, but they are not the missing step. Serre's proof
reduces to the diagonal in the complete tensor product, which needs Cohen's structure theorem; nothing in the
inventories supplies it. I list it so the next search does not over-rate it. Positivity in equal characteristic
(fc `intersectionMultiplicity_pos_of_equalCharacteristic`) sits behind the same barrier.

## Rejected, and why

- **Brouwer and invariance of domain** (`AutoClose.brouwer_fixed_point_holds`, `invariance_of_domain_holds`). No
  open Atlas row or unproved fc statement uses them as the key step. The fc inscribed-rectangle theorem
  (`InscribedSquare.lean`, `exists_inscribed_rectangle`, Vaughan) needs RP² ↛ ℝ³, which Brouwer does not give.
  Borsuk's problem (`BorsukConjecture.lean`, Atlas `erdos-505`) needs Borsuk–Ulam, and its open cases are
  combinatorial. Hilbert's fifth problem, Bing–Borsuk and the Hadwiger–Nelson rows need far more topology. Nash
  equilibria, Perron–Frobenius, Poincaré–Miranda and KKM are unformalised *theorems* with no Atlas or fc row.
  They make a possible Mathlib PR, not a target here.
- **Hörmander, Osgood, psh theory beyond #4.** The Levi problem and Ohsawa–Takegoshi-type statements have no Atlas
  or fc row (the Atlas has no openness, Demailly–Kollár or Levi entries). The repo's
  `L2ExtensionLogCanonical` is a bespoke atlas-based statement, not Ohsawa–Takegoshi.
- **Jacobian-conjecture reductions.** The fc open case is n = 2, with no RH-repo input. Injective holomorphic ⇒
  biholomorphic gives a holomorphic inverse, not a polynomial one. Ax–Grothendieck is already in Mathlib.
- **Igusa rationality, weak factorisation, Hodge-theoretic statements.** None has an Atlas or fc statement.
  Igusa's p-adic rationality also needs p-adic integration over a resolution, which is XL.
- **Étale cohomology / Gysin, coherent finiteness, Kawamata–Viehweg standalone.** All are on internal
  definitions, there is no target row, and the Weil and trace-formula pieces are unproved skeletons (inventory 05).
- **Markov brothers' inequality.** Erdős 115 is already formally proved (plby). Erdős 1133, 1038, 1150 and 1129–1132
  are about interpolation, sublevel sets or Littlewood polynomials, where Markov is not the missing step.
  Sendov's and Smale's mean-value problems need other tools.
- **Lie–Trotter, Minkowski II, Harder–Narasimhan, Mahler volume, sphere packing.** No target where these decide
  anything.
- **Burnside, Brauer–Nesbitt, Skolem–Noether, Jordan p-cycle, Witt.** The group-theory fc rows (Kourovka 8.8,
  21.149, 20.51; Fernandes, `Arxiv/2605.12342`) are proved already or unrelated. The S_n inverse Galois variant is
  already proved. The Jordan p-cycle theorem mainly feeds Galois groups of polynomials over ℚ, which is number
  theory (another agent's slice).
- **Abelian-scheme laws, #E[n], Néron–Ogg–Shafarevich, semistable reduction, Poisson, Casselman–Shalika, local
  converse.** These are arithmetic (torsion, supersingular primes, Langlands rows) and belong to the other two
  agents.
- **Auslander–Reiten in general, Serre positivity, small CM in general, Hartshorne, Pierce–Birkhoff, Bass,
  Nagata.** These are open, and the lemmas give no partial result beyond #3, #5 and #6.
