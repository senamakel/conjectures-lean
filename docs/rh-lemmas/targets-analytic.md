# Matching the riemann-hypothesis analytic toolkit to targets

Slice: analytic number theory. Date 2026-11-24. RH repo at `507a75d91d` (toolchain `v4.36.0`, same as ours).
Paths are relative to `riemann-hypothesis/src/`. I ran no lake or lean. Declaration names come from
reading the source; check each with `#check` before importing it. "GRH" means
`LFunction_ne_zero_of_half_lt_re : DirichletLNonvanishingRightOfHalf` (`Statements.lean:10`).

## Three findings that shape the ranking

1. **GRH plus the repo's uniform truncated explicit formula gives one hub lemma for many targets.** That lemma is
   `|ψ(u,χ) − δ_χ u| ≤ C √u log²(qu)`, uniform in the modulus q. It follows from
   `GlobalTheory.ExplicitFormula.truncated_explicit_formula` (`…/GlobalInterpolation/TruncatedExplicitFormula.lean:16`)
   and `GlobalTheory.ZeroWindow.count_zeros_window` (`…/GlobalInterpolation/FinsumMemLeOfSubset.lean:31`). I opened
   both. Each is `∃ C > 0, ∀ N [NeZero N] χ, χ.IsPrimitive → …`, so the constant is uniform in the conductor N, and
   multiplicities are counted with `analyticOrderNatAt`. The explicit formula carries an extra term
   `Σ_{|Im ρ|<1} m_ρ/‖ρ‖`. Under GRH, |ρ| ≥ 1/2, so the window count bounds that term by C log 2N. The
   formula is stated for primitive χ only. Reducing an imprimitive χ to its primitive one costs O(log q · log u),
   which is routine bookkeeping. The bound covers N = 1, so ζ is included. **About six targets below reduce to
   this one lemma.** Build it once as a library, the way NEXT_TARGETS already plans the zero-counting library.
2. **Most repo constants are existential (`∃ C`).** So the repo helps with O-type statements and does not help
   with statements that end in a finite check. Mills (#7), the Weinberger finite range (#1), and the LLS and
   Bach constants (#3, #12, #13) do not get cheaper. A few constants are explicit:
   - Brun–Titchmarsh has C = 48 (`BrunTitchmarshExistsConst.lean:53`).
   - The Perron kernel has C = 3.
   - Mertens' first theorem has the constant log 4 + 4.
   - π(y) < 1.26 y/log y is explicit.
3. **Two published Lean proofs are complete except for axioms that the repo now discharges.** Both repos are
   Apache-2.0, so vendoring is allowed with a NOTICE (rule 11).
   - **Erdős 696** (davidturturean/erdos-696, Lean v4.28) axiomatises Siegel–Walfisz, Brun–Titchmarsh and Mertens.
   - **Erdős 694** (Shashi456/erdos-formalizations `Erdos/P694`, Lean v4.27) axiomatises Linnik and Mertens' product theorem.

**Tier note.** AGENTS.md puts anything that imports riemann-hypothesis in tier U. Targets 2, 3, 4 and 10 use only
the repo's unconditional lemmas and never RH, but they still inherit the trust caveat about the untrusted build
cache. I mark them **U₀**: tier U, with no RH used. A README could say so, and AGENTS.md might want this nuance
written down.

## Ranked table

| # | Target | Kind | Source + Atlas id / formal-conjectures file | RH-repo lemmas used (decl, path) | What is still missing | Expected tier | Effort |
|---|---|---|---|---|---|---|---|
| 1 | **Bombieri–Vinogradov, θ < 1/2, via GRH** | 2 | Bombieri 1965 / A.I. Vinogradov 1965; under GRH it is immediate. Atlas `wiki-elliott-halberstam-conjecture`; fc `Wikipedia/ElliottHalberstamConjecture.lean`, `elliott_halberstam.variants.bombieri_vinogradov` (fixed x, max over a, π-form, no max over y) | GRH; `truncated_explicit_formula`; `count_zeros_window`; `Claim.prim_zero` / `UpperTheory.Top.imprimitive` (`CharacterBoxes/ClaimStrip.lean`, `Imprimitive.lean`) for primitive reduction | Hub lemma (finding 1). Character orthogonality for max_a; prime powers and p ∣ q; ψ→π by partial summation; then Σ_{q≤x^θ} E ≤ x^{θ+1/2} log²x | U | M |
| 2 | **Erdős 696** (H(n)/h(n) → 2 for almost all n) | 1 | fc `ErdosProblems/696.lean` `erdos_696` (solved); Atlas `erdos-696`; Lean proof davidturturean/erdos-696 `Erdos696/AnalyticInputs.lean` (3 axioms) | `Formalism.ZeroFreeDirichlet.siegelWalfisz` (`LandauZeroFreeBounds/SiegelWalfiszAPOfSiegelLower.lean:38`) plus `chebyshev_progression_orthogonality`; `GlobalTheory.Lin.brun_titchmarsh_const` (`…/BrunTitchmarshExistsConst.lean:53`); `GlobalTheory.mertens_first_vonMangoldt` (`…/IwasawaDecomposition/LogFactorialEqSumVonMangoldtMulDiv.lean:64`) | ψ(x,χ)-form S–W → π(t;q,a) − li t/φ(q) form (orthogonality + partial summation). BT matches the axiom exactly with x = 0. Mertens 2nd theorem with O(1/log t) by partial summation from the 1st. Port v4.28 → v4.36 | U₀ | M |
| 3 | **Erdős 694** (max f_max/f_min = (e^γ+o(1)) log log x) | 1 | fc `ErdosProblems/694.lean` `erdos_694` (solved); Atlas `erdos-694`; Lean proof Shashi456 `Erdos/P694/Proof.lean` (axioms `linnik_dvd`, `mertens_product`) | `UpperTheory.T3.smallOne` (`AutomorphicArithmetic/ShortNorms/Primes.lean`; M ≥ 2 ⇒ p ≡ 1 mod M, p ≤ M^A); `mertens_first_vonMangoldt`; our robin-rh `Robin.mertens_const_eq_gamma` | Real exponent A → ℕ exponent ⌈A⌉, and the M = 1 case. Mertens 3rd = convergence (from the 1st) + robin-rh's constant identification. Port v4.27 → v4.36 | U₀ | S–M |
| 4 | **Linnik for p ≡ 1 (mod n)** | 1 | fc `ErdosProblems/456.lean` `erdos_456.variants.linniks_theorem`; Atlas `erdos-456` | `UpperTheory.T3.smallOne` (or `UpperTheory.Lit.linnik`, `ThetaCorrespondence/Linnik.lean:146`) | Unfold `sInf`; handle n ≤ 1; convert to `=O[atTop]` | U₀ | S |
| 5 | **Pollack 2017 Thm 1.3 under GRH, then Erdős 1141** | 2 | fc `ErdosProblems/1141.lean` `erdos_1141.variants.pollack_1_3` and `.mertens_third`, then `erdos_1141` (solved; deduction formalised in Jayyhk/erdos-lean, licence not checked); Atlas `erdos-1141` | Hub lemma for one quadratic χ (and the trivial one, which `IsQuadratic` allows) | At y = m^{1/4+ε}, Σ_{ℓ≤y}(1+χ(ℓ)) log ℓ = y + O(√y log²(my)), so the count is ≫ y/log y ≥ log^A m. Weak Mertens 3rd, 1/(3 log n) (S with item 3's Mertens work). Port the deduction. The unconditional proof needs Burgess + Siegel, which the repo lacks | U | S–M (+M port) |
| 6 | **Erdős 1961: mean of n₂(p) = Σ p_k/2^k** | 2 | fc `ErdosProblems/980.lean` `erdos_980.variants.erdos_two` (solved); Atlas `erdos-980`; Martin–Pollack JLMS 2012 eq. (1.1) confirms the constant | Hub lemma for real characters mod 8∏_{i≤K}p_i; ankeny-grh `leastNonresidue_of_GRH` for the tail n₂(p) ≪ log²p | Quadratic reciprocity bookkeeping (Mathlib); density 2^{−k} via Σ_S χ_S(p); choose K ≈ 3 log log x/log 2; uniformity in K | U | M |
| 7 | **NEXT_TARGETS #2 / #5 / #8 / #9 re-costed** | 2 | NEXT_TARGETS; fc `Wikipedia/DensityHypothesis.lean` (uses `Complex.zeroCountOn`) | Hub lemma at N = 1; `count_zeros_window` summed over unit windows ⇒ N(T) ≪ T log T, with multiplicity | #2: the O-form ψ(x) = x + O(√x log²x) is **S**. Schoenfeld's 1/(8π) stays M–L. #5: gaps O(√p log²p) is **S** after #2; Cramér's √p log p needs a smoothed formula. #8: **S** (N(σ,T) = 0 for σ > 1/2, plus a bridge from `analyticOrderNatAt` to `zeroCountOn`). #9: Σ 1/\|ρ\|² < ∞ is now free; "infinitely many zeros" is still missing | U | S each (#9: M) |
| 8 | **NEXT_TARGETS #10 Mertens M(x) = O(x^{1/2+ε})** re-costed | 2 | NEXT_TARGETS #10 (no fc statement) | `GlobalTheory.PerronKernel.truncated_perron_kernel` (`…/TruncatedPerronKernel.lean:351`, C = 3): the sharp-cutoff Perron that #10 lacked. Also `logDeriv_LFunction_strip` / `ZetaWide.main` | 1/ζ ≪ \|t\|^ε on σ ≥ 1/2 + δ under RH (lindelof-rh territory); contour shift with 1/ζ (rectangle residue `GlobalTheory.ResRect.residue_rectangle` exists) | U | M (was M–L) |
| 9 | **Littlewood 1914: π(x;4,3) − π(x;4,1) changes sign infinitely often** | 2 | fc `Wikipedia/ChebyshevBias.lean` `littlewood_mod_four_sign_changes` (solved); not in the rejected list (Knapowski–Turán is a different item) | GRH for χ₄; `Deduction.landau_window` / `poleData_char` (`DedekindLFunctions/LandauTheorems/`) only as a template | A Landau lemma for one-signed Dirichlet integrals, in log L form (the repo's version is the L′/L pole-residue form). The argument compares orders: m ≥ 1 at a zero 1/2+iγ against the ½ log 1/(σ−½) from ζ(2s). Also needed: existence of a non-real zero of L(s,χ₄), certified L(1/2,χ₄) ≠ 0, and the prime-square bias | U | L |
| 10 | **Weak unconditional Bombieri–Vinogradov (some level θ₀ > 0, Rényi-type)**; full unconditional B–V | 1 | Rényi 1948; Bombieri 1965; same fc statement weakened (rule 3) | `GlobalTheory.ZeroDensityMult.zero_density_mult` / `ZeroDensityBox` (≤ CQ^{1/4} characters with a zero in Re > 1−1/400, \|Im\| ≤ Q); `truncated_explicit_formula`; `siegelWalfisz`; for the full version also `GlobalTheory.MultSieve.multiplicative_large_sieve`, `GlobalTheory.HybridLargeSieve.hybrid_large_sieve` | Weak version (my sketch, unverified): trivial bound on the bad characters, zeros with β ≤ 1−1/400 for the rest, giving θ₀ ≈ 1/800. Full version: Vaughan's identity and Type I/II bilinear estimates (not in the repo) | U₀ | weak M–L; full L–XL |
| 11 | **Titchmarsh divisor problem** Σ_{p≤x} d(p−1) ~ (ζ(2)ζ(3)/ζ(6)) x | 2 | Titchmarsh 1930 (under GRH), Linnik 1961 / Halberstam 1967 (unconditional) *(citations from memory, unverified)*; no fc statement found | Item 1 + `brun_titchmarsh_const` | Dirichlet hyperbola split, Σ_{d≤√x} π(x;d,1) via item 1, large d via BT and symmetry | U | M |
| 12 | **Heilbronn / Siegel: h(−d) ≫_ε d^{1/2−ε}, so h(−d) → ∞** | 1 | Siegel 1935; Heilbronn 1934; Atlas `wiki-class-number-problem` (fc `ClassNumberProblem.lean` has only Stark–Heegner) | `Formalism.ZeroFreeDirichlet.siegelLower` (`FinalSiegel.lean:21`); `GlobalTheory.QuadraticZeta.LFunction_one_and_mean_log_eta` (L(1,χ) = πh/√d), `dedekindZeta_eq_mul_LFunction` (`…/HomogeneousIdeals/`) | Bridge from repo-internal `IsKroneckerChar` / `IsIdealClassPoint` to Mathlib `classNumber`. Ineffective, so this gives no finite list. The same class-number-formula lemmas lower the "Mathlib class groups are thin" cost of NEXT_TARGETS #1, step 2 | U₀ | M |
| 13 | Erdős 971 solved variant `many_small` (Erdős 1949) | 1 | fc `ErdosProblems/971.lean`; Atlas `erdos-971` | `brun_titchmarsh_const`, `GlobalTheory.T.arithmeticLargeSieve_one_residue_class_per_prime` | An upper-bound sieve for prime pairs p, p+kd (two classes per prime). The repo's arithmetic large sieve allows one class per prime; Mathlib's `SelbergSieve` framework might fill the gap | U₀ | M–L |

## Top ten in detail

**1. Bombieri–Vinogradov via GRH.** This is the best ratio of value to cost. The fc statement asks for a fixed x,
`E x q = ⨆ a : (ZMod q)ˣ |π(x;q,a) − π(x)/φ(q)|`, and Σ_{q ≤ ⌊x^θ⌋} E ≤ C x/log^A x. It needs no maximum over
y ≤ x, which is the part that forces Vaughan and the maximal large sieve in the unconditional proof.

- **Proof sketch.** Under GRH, the hub lemma gives E(x;q) ≪ √x log²(qx) after orthogonality, so the sum is
  ≪ x^{θ+1/2} log²x, and that is ≪ x/log^A x for every θ < 1/2. Moving from ψ to π uses only fixed-t bounds
  inside ∫ θ(t)/(t log²t) dt, so it needs no maximum over y either.
- **What I checked in the source.**
  - Uniformity in N, χ, T and u.
  - The formula covers ζ (N = 1).
  - The `psi0` definition is Σ_{n ≤ ⌊u⌋} Λχ − [N=1]u.
- **Tier.** Put it in the main library as `bombieri_vinogradov_of_GRH (hGRH : DirichletLNonvanishingRightOfHalf)`
  (C), then discharge GRH in one line in `Unconditional/` (U).
- **Unlocks.** The hub lemma also feeds 5, 6, 7 and 11.

**2. Erdős 696.** The repo discharges all three axioms of a complete public proof. Item by item:

- **Brun–Titchmarsh.** The repo's `primesIoc 0 t` filtered by p ≡ a [MOD q], with y = t ≥ 2q, gives exactly
  `piMod t q a ≤ C t/(φ(q) log(t/q))`. Confirm `piMod`'s floor convention.
- **Siegel–Walfisz.** The repo states it for ψ(x,χ) with q ≤ (log x)^A and a uniform c, C, and with
  "if χ = 1 then x" as the main term. Getting the axiom's π-form with li t/φ(q) takes orthogonality plus partial
  summation; the error keeps the exp(−c√log) shape.
- **Mertens.** The axiom wants |Σ_{p≤t} 1/p − log log t − M| ≤ C/log t. It follows from the repo's
  |Σ Λ(n)/n − log y| ≤ log 4 + 4 by Abel summation. Check whether pinned Mathlib already has it; I did not.
- **Remaining work.** The rest is a toolchain port from v4.28.

**3. Erdős 694.** The two axioms map as follows:

- **`linnik_dvd`** comes from `smallOne`. Its exponent is a real A ≥ 1 with M ≥ 2; use L = ⌈A⌉, and take ℓ = 2
  for M = 1.
- **`mertens_product`** (∏ p/(p−1) ~ e^γ log y) needs convergence of Σ_{p≤x} −log(1−1/p) − log log x.
  - Convergence follows from Mertens' 1st theorem.
  - robin-rh's `mertens_const_eq_gamma` then identifies the limit as γ; it was proved unconditionally from
    convergence.
- **Value.** It turns the README's "conditional on two axioms" into a closed result, and both inputs already exist.

**4. Erdős 456 Linnik variant.** This takes one lemma and maybe 50 lines, and makes a good smoke test of the
import pipeline. Goal: `∃ L, (fun n ↦ (p n : ℝ)) =O[atTop] (fun n ↦ n ^ L)`, where `p n = sInf {k | k.Prime ∧ k ≡ 1 [MOD n]}`.

**5. Pollack Theorem 1.3 under GRH.** Confirmed statement: for ε, A > 0 there is m₀ such that every quadratic χ mod
m > m₀ has at least (log m)^A primes ℓ ≤ m^{1/4+ε} with χ(ℓ) = 1 (Proc. AMS 145 (2017) 2815–2826,
arXiv:1508.05035).

- **Why the original is out of reach.** Pollack's proof uses Burgess (Norton) and Siegel; the repo has no
  Burgess bound.
- **The GRH route.** It is one application of the hub lemma, plus the reduction from imprimitive to primitive
  (the primes ℓ ∣ m number at most log m).
- **Payoff.** With `mertens_third` (weak: ∏(1−1/p) ≥ 1/(3 log n)), the published deduction
  makes `erdos_1141` tier U.
- **Before starting.** Check the licence of the Jayyhk/erdos-lean deduction.

**6. Erdős 980, k = 2.** Confirmed: lim π(x)^{−1} Σ_{2<p≤x} n₂(p) = Σ p_k/2^k ≈ 3.67464 (Erdős, Mat. Lapok 12
(1961); Martin–Pollack, JLMS 2012, eq. (1.1)).

- **Erdős's proof** uses quadratic reciprocity for fixed k and Linnik's large sieve for the tail.
- **The GRH substitute.**
  - For the main range, the hub lemma for the 2^k products of Kronecker symbols mod 8∏p_i.
  - For the tail, ankeny-grh's n₂(p) ≤ (21/5) log²p together with #{p ≤ x : p_1,…,p_K all residues} ≪ 2^{−K}π(x).
- **Reuse.** It reuses our own repo, and the fc statement fixes the exact constant.
- **What is out of reach.** General k (Elliott) needs Chebotarev in the non-abelian Kummer fields
  ℚ(ζ_k, p^{1/k}), which GRH for Dirichlet L does not give. That is the same obstruction as artin-grh.

**7. Re-costing NEXT_TARGETS #2, #5, #8, #9.** The repo supplies the zero-counting library and the truncated
explicit formula that round 2 planned to build. Its constants are not explicit, so:

- **#2.** The O-form of von Koch is now a short corollary. Schoenfeld's explicit `√x log x/(8π)`, and Mills (#7)
  built on it, still need erdos-985's explicit machinery.
- **#5.** The cheap form is gaps O(√p log²p), one log weaker than Cramér. State it as a deviation (rule 3).
- **#8.** `zeroCountOn` counts with multiplicity, as `count_zeros_window` does, so only a bridging lemma is needed.
- **#9.** Summability is solved. Strict positivity still needs infinitely many zeros (Hadamard in erdos-985, or a
  lower bound for N(T)).

**8. NEXT_TARGETS #10, the Mertens function.** The recorded blocker was "a sharp-cutoff Perron formula, which
Mathlib lacks". `truncated_perron_kernel` is that kernel lemma, for any y > 0, y ≠ 1, c > 0, T ≥ 1, with
constant 3. What remains:

- the 1/ζ bound under RH (Littlewood; lindelof-rh's Borel–Carathéodory work);
- a contour shift for Σ μ(n) n^{−s} = 1/ζ(s), using the repo's rectangle residue theorem.

This moves the effort from M–L to M, and #16 (Riesz, Hardy–Littlewood) follows after it.

**9. Littlewood's mod-4 sign changes.** The fc statement exists and is solved. GRH for χ₄ removes Littlewood's case
split. The argument (Ingham-style; compare Bateman et al., arXiv:1910.08983, Lemma 2.1) runs:

1. Suppose the race difference is eventually one-signed.
2. Landau's lemma then makes Σ_p χ₄(p) p^{−s} analytic on Re s > 1/2, and gives |F(σ+iγ)| ≤ |F(σ)| + O(1).
3. At a zero 1/2+iγ of order m ≥ 1, log L contributes m·log 1/(σ−½). But F(σ) grows only like
   ½·log 1/(σ−½), which comes from ζ(2s). Since m ≥ 1 > 1/2, this is a contradiction.

What is missing:

- Landau's lemma for Dirichlet integrals with a one-signed integrand. The repo's `landau_window` needs pole data
  with positive residues, which does not fit log L, so expect a rewrite rather than a reuse.
- A non-real zero of L(s,χ₄).
- A certified L(1/2,χ₄) ≠ 0 (≈ 0.6677; unverified).

Effort L.

**10. Weak or full unconditional B–V.** This matters only if we want B–V to survive a failure of the RH repo's main
theorem. The weak version (some small fixed level) looks reachable from the zero-density box. The 1/400 and Q^{1/4}
constants are existential, so θ₀ is too. The full θ < 1/2 version needs Vaughan's identity and bilinear estimates.
The repo has the multiplicative and hybrid large sieves but not those two pieces. Not recommended before item 1.

## Rejected, and why

- **Vinogradov's three primes for large n, fc `ternaryGoldbach`, NEXT_TARGETS #6 (DETZ).** The minor arcs need
  Vaughan's identity and exponential sums over primes, and the repo has neither. Only the major arcs get cheaper
  (S–W, or GRH). #6 is unchanged.
- **Elliott–Halberstam proper (θ ≥ 1/2).** GRH does not imply it; open.
- **Chowla's least-prime conjecture, p(a,q) ≪ q^{1+ε}.** Open even under GRH, which gives q^{2+ε}. The repo's
  Linnik exponent is existential, so Xylouris's L = 5 is out of reach too.
- **Erdős 695 (q_k^{1/k} → ∞, and the upper-bound variant).** Linnik iterates only to tower-type upper bounds,
  which is the wrong direction and the wrong size.
- **Erdős 971 main statement and 456 parts i–iii.** Open, and no analytic lemma here bears on them (variant 13
  aside).
- **"No Siegel zeros".** It is a one-line corollary of GRH, but I found no fc statement, so there is little to
  gain. Note it in passing.
- **Explicit-constant targets (#1 Weinberger finite check, #7 Mills, #12 LLS upgrade, #13 explicit L(1,χ)).** The
  repo's constants are existential, so no change in tier or cost. Exception: #1's class-number-formula step gets
  cheaper (row 12).
- **Erdős 980 for general k, unconditional Artin (Heath-Brown).** Both need non-abelian Chebotarev under GRH
  (rejected as for artin-grh). Heath-Brown's result also needs Chen's sieve and B–V: XL.
- **Jutila-type zero density over all σ.** `GlobalTheory.Mem.An.Jutila` is stated, not proved. The only density
  results are near σ = 1 at fixed constants.
- **Green 47 and Erdős 1202.** Green 47 is solved by counterexample (KitaKen1). Erdős 1202 is resolved, and the
  repo's one-class arithmetic large sieve does not reach it.
- **Knapowski–Turán, Rubinstein–Sarnak, Montgomery pair correlation.** Unchanged from the existing rejected list.
  The toolkit adds no oscillation or LI input.

## Caveats

- **Nothing was typechecked.** The statements I opened by hand are:
  - `truncated_explicit_formula`, `count_zeros_window`, `SiegelWalfisz` and `siegelWalfisz`;
  - `brun_titchmarsh_const`, `SmallOne` / `smallOne`, `Linnik`;
  - `mertens_first_vonMangoldt`, `truncated_perron_kernel`, and GRH.

  The rest come from the inventories.
- **Import cost.** It may be possible to import single leaf modules (e.g. `TruncatedExplicitFormula`, about 203
  repo files in its closure) instead of `Main`, which would cut RAM and cache needs. I have not tested whether
  `lake` still needs the full 93 GB cache for that.
- **Search gap.** The fc code search hit the GitHub rate limit partway through, so the absence of fc statements
  for Titchmarsh's divisor problem, Heilbronn and Siegel zeros is *(unverified)*.
