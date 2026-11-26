# Lane `w3-openai-corollaries`: machine-proved theorems as premises for unstated corollaries

**PAUSED, INCOMPLETE** (owner's instruction, 2026-11-26). Research only; no Lean, no repository
edits except this file and `w3-openai-corollaries.edges.jsonl`. Claims not checked against a
primary source are marked *(unverified)*. Scripts: session scratchpad `w3scripts/` (`v417.py`,
`tansum.py`). openai/math read at `3344da599` (2026-11-25) via the local partial clone and `gh api`.

## In one line

Two class-A candidates, both minor: (1) **Σ tan(n)/n² converges** (an MSE question of 2013 whose
only answer wrongly claims divergence), with the full criterion for `Σ |tan n|^b/n^a` and
`Σ 1/(n^a |cos n|^b)`, from μ(π) = 2 in a few lines; (2) **Erdős 417 partial: `liminf V(x)/V'(x) > 1`**,
from OpenAI's Lean least-preimage theorem. Neither settles a formal-conjectures statement as
written. Two class-B items (zeta-23 neighbours via RH). Much of the ground was not reached.

## Class A

### A1. Σ tan(n)/n² converges; the tan/sec/cot analogue of OpenAI's Corollary 5.2 (effort S)

- **Source of the question.** Math.SE 470527, "Does the sum Σ tan n / n² converge?" (2013, score 39):
  two answers, one claiming divergence by an invalid series manipulation, one a hint saying the
  question was undecidable with μ(π) ≤ 7.6. Math.SE 616767 asks for which real z `Σ tan(nz)/n²`
  converges; its accepted answer only shows divergence when μ(z/π) > 3. Not in formal-conjectures,
  not in OEIS (A249836 / A088306 / A000503 are about `tan n > n`, see below).
- **Premise.** μ(π) = 2: `OAI.PiExponent.pi_eventual_lower_bound : PiEventualLowerBound`
  (openai/math, Apache-2.0), already vendored and ported to Lean v4.36.0 / Mathlib fc4f59e5 in
  `conjectures/cookson-hills/Vendor/` (869 files). No hypothesis needed: tier D.
- **Deduction.** `|sin 2n| = 2|sin n||cos n| ≤ 2|cos n|`, so `|tan n| ≤ 1/|cos n| ≤ 2/|sin 2n|` and
  `|tan n|/n² ≤ 8/((2n)²|sin 2n|)`. Summing over n is a subseries of `8 Σ_m 1/(m²|sin m|)`, which
  converges by OpenAI's Cor. 5.2 with (a, b) = (2, 1) (a > max{1, b}). So the series converges
  **absolutely**. In general, with μ(π) = 2: `Σ |tan n|^b/n^a`, `Σ 1/(n^a|cos n|^b)` and
  `Σ 1/(n^a|tan n|^b)` converge iff `a > max{1, b}`. Convergence: the same doubling (cos, tan) or
  `|tan| ≥ |sin|` (cot side). Divergence for `1 < a ≤ b`: consecutive convergents `(p_j, q_j)`,
  `(p_{j−1}, q_{j−1})` of π form a ℤ-basis, so one of them or their sum has p even and q odd;
  that gives infinitely many n = p/2 with `|cos n| ≤ C/n`. For a ≤ 1, compare with `Σ n^{-a}`
  (cot/tan: equidistribution). Hence also `Σ tan(n)/n^{1+ε}` converges absolutely and `Σ tan(n)/n` diverges.
- **Numerics (done, float64, glibc range reduction).** `Σ_{n≤N} tan n/n²` = 0.836808 (N = 10),
  −1.080981 (10²), −1.079505 (10³), −1.079413 (10⁴), −1.079414 (10⁵), −1.079417 (10⁶ … 10⁸).
  `Σ |tan n|/n²` = 4.594271 (10⁶) → 4.594281 (10⁸). `Σ |tan n|/n^1.5` = 11.4492 (10⁷) → 11.4544
  (10⁸), still creeping as expected for a = 1.5. Largest `|tan n|/n` per block of 10⁷ up to 10⁸:
  1.0105 at n = 37362253 and 1.9955 at n = 42781604, matching OEIS A249836/A088306. Nothing
  contradicts the deduction.
- **Novelty search (2026-11-26).** The OpenAI paper states only the sin family (Cor. 5.2). Exa web
  searches ("Σ tan(n)/n² converge", "μ(π)=2 corollary tan/sec"): only MSE 470527 and 616767,
  John D. Cook's blog of 2026-10-07, Wikipedia "Irrationality measure" (rev. 2026-10-20),
  aiXiv's Flint Hills page, Dan arXiv:2609.12338, López Zapata arXiv:2603.09719 (defines
  `Σ tan(n/2)/n³`; that one follows trivially from Cor. 5.2 with b = 1). GitHub code search for
  `tan n / n^2`, `tan(n)/n^2`, `Real.tan (n`: nothing relevant. Not found.
- **Catch.** A weak source (a Math.SE question), and the step is so short that anyone reading
  Cor. 5.2 could write it down. Lean cost: OpenAI's Lean has the spacing lemma only for (3, 2)
  (`Analysis/FlintConsequence.lean`, `DyadicSpacing.lean`); (2, 1) needs the b = 1 case with
  its `log K` factor. Then reuse cookson-hills' doubling lemma. One to two days.

### A2. Erdős 417, partial: `liminf V(x)/V'(x) > 1` (effort S given the OpenAI Lean)

- **Statement.** erdosproblems.com/417: with `V'(x) = #{φ(m) : m ≤ x}`, `V(x) = #{φ(m) ≤ x}`, "Does
  `lim V(x)/V'(x)` exist? Is it > 1?" Open, last checked on that page 2026-11-22. formal-conjectures
  `ErdosProblems/417.lean`, `erdos_417.parts.i` and `erdos_417.parts.ii` (`research open`, both
  require the limit to exist, `ENNReal`).
- **Premise (Lean, Apache-2.0, Lean v4.34.1 / Mathlib d13f23b).** `OAI.TotientAsymptotic.weighted_totient_asymptotic`
  and `weighted_totient_one_two` (`lean/OAI/NumberTheory/TotientAsymptotic/UnconditionalMain.lean`,
  Comparator `TotientAsymptotic.lean`). For k = 1: `N₁(x) = #{v ≤ x totient : x < ℓ(v) ≤ 2x}`
  satisfies `N₁(x) ≥ c·V(x)` eventually, with c > 0.
- **Deduction.** `φ(n) ≤ n`, so `V'(x) = #{v ≤ x : ℓ(v) ≤ x}` and `V − V' = Σ_{k≥1} N_k ≥ N₁ ≥ cV`.
  Hence `V'/V ≤ 1 − c` and `liminf V/V' ≥ 1/(1−c) > 1`. Upper side: Lean
  `bounded_ratio_positive_proportion` (`BoundedRatioValues.lean`) with seed d = 1, k = 0
  (`pptBoundedFiberPropagation` is proved in `FiberPropagationInput.lean`) gives a, b, η > 0 with
  `#{v ≤ x : a ≤ ℓ(v)/v ≤ b} ≥ ηV(x)`. Applying it at x/b, together with Lean's
  `V(cx)/V(x) → c`, gives `V'(x) ≥ (η/b − o(1))V(x)`, so `limsup V/V' < ∞`. Together:
  `1 < liminf V/V' ≤ limsup V/V' < ∞`. A limit, if it exists, is finite (against Erdős's
  suggestion that it might be infinite) and exceeds 1.
- **Numerics (done, exact sieve to 7·10⁷).** `V(10⁶) = 180184` (matches the literature),
  `V'(10⁶) = 163861`. Ratio `V/V'` at x = 10³…10⁷: 1.1023, 1.0991, 1.1000, 1.0996, 1.1000;
  `N₁/V ≈ 0.091`, `N₂ = 0` up to 10⁷, `max ℓ(v)/v = 2.041`. Consistent with liminf > 1.
- **Prior art (important).** Not clean. (i) erdosproblemaday.com/report/417 (2026-07-28):
  `limsup V/V' > 1` from Ford's Theorems 4 and 8. (ii) Plasma AI's wiki
  (`plasma-ai/erdos` `wiki/problems/arithmetic_functions/E0417/_index.md`, updated 2026-10-19)
  writes down `V − V' = Σ_k N_k` and records `N₁ ≍ V` from the OpenAI release, but does not state
  the liminf. It also records `V ≍ V'` as known (Pollack–Pomerance–Treviño quoting Ford) and an
  October note (LeanMeanBean/417) claiming `limsup V/V' < 2.195202`. It reduces existence of the
  limit to phase-constancy of `A(f₀; s)/A(1; s)`, which is open. (iii) The erdosproblems.com forum
  thread has no post after May 2026. (iv) formal-conjectures PRs for "417": #1781, #4739 (statement
  fixes) and #2914 (closed, loophole). (v) GitHub code search `erdos_417`/`Erdos417`: benchmark
  copies, plus rjwalters/lean-genius, which takes the conjecture as an axiom; no proof. (vi) 1337
  solved-conjectures at `43152d52`: no entry. (vii) The OpenAI paper does not mention V′.
  Verdict: the liminf is **not found stated**, but it is one line from published material, and
  the limsup < ∞ half is published (Ford via PPT). Low value: it settles neither fc statement.
- **Catch.** fc's `parts.ii` needs existence. Existence is the phase question, and the ratio
  could oscillate. Porting the 810-file TotientAsymptotic tree (3.3 MB of Lean) from v4.34.1 is
  M–L; as a hypothesis (tier H/C) it is S.

## Class B

- **zeta-23 neighbours.** fc `Paper/RiemannZetaZeros.lean`: `riemannZeta.simple_prop_lt` (> 0.6725)
  and `distinct_prop_lt` (> 0.8362) are `research open`. Under RH they are published: Bui–Heath-Brown
  2013 (19/27 simple, 0.84665 distinct), Chirre–Gonçalves–de Laat 2020 (0.6792, 0.8477), and Cl26
  §7.3 itself (0.85082 distinct on RH). RH is Lean-proved here, so they are now theorems, but only
  through those papers (XL in Lean; Cl26's unconditional method is capped near 0.682 by its own
  §7.2 Lean ceiling). Also: with RH, `Ns ≥ 2Nd − N` (exact), so any distinct-proportion bound
  above 0.8362 gives a simple-proportion bound above 0.6725. That is cheap once a distinct bound
  exists, but every known one needs BH13 or the triple correlation. The Dirichlet-L analogues in
  the same file were not checked.
- **Chen–Pearse (arXiv:1807.02955).** `sup Φ = 2μ(π) − 2` with `Φ = {γ : limsup |cos k|^{k^γ} = 1}`,
  so `sup Φ = 2` now follows. It is immediate from their published theorem, and the borderline
  γ = 2 is equivalent to π not being badly approximable, which is still open.

## Class C / rejected (recorded)

- Generalised Flint Hills `Σ 1/(n^a|sin n|^b)`, iff `a > max{1,b}`: OpenAI Cor. 5.2 (published).
- `1/(n² sin n) → 0`: Math.SE 20555 answer, updated Oct 2026 (published).
- Borwein sine series: AxiomMath Lean, fc solved. Flint/Cookson Hills: done (cookson-hills).
- `tan n > n` infinitely often (A249836, Bellamy–Lagarias–Lazebnik) and Forgues' `tan n > kn`:
  μ(π) = 2 gives only the upper side (`|tan n| < n^{1+ε}` eventually), not these.
  `liminf n|sin n| = 0` and the growth laws `log a(n)/n → π` (A249836) and `π/2` (A088306) are not
  decided by μ(π) alone (bounded partial quotients and Lévy-type statistics).
- OEIS A064313 (`⌊(n/4)cot(π/n)⌋ = ⌊n²/(4π) − π/12⌋`): needs joint approximation of π and π², not μ(π).
- Tao constant 7b (μ(Γ(1/4))): not a function of μ(π).
- Ostmann (OAI 013) ⇒ "primes ≠ A+B+C up to finitely many": immediate (A + (B+C)), and I found no
  statement of it as open.
- OAI 024 ⇒ Erdős 416: fc already links it. OAI 028 ⇒ Erdős 952: linked. OAI 021 ⇒ Erdős 970,
  687(iii): linked or done (30k30/scholia). OAI 025 ⇒ Erdős 148 (`log log F(k) = Θ(k)`): an estimate,
  claimed in the OAI abstract; fc 148 is a `question value` statement, not checked further.

## Not reached

- (1) OpenAI headline results other than 017, 024 and 013/021/025/026/028 at title level. The 246
  Lean families' cheap corollaries against OEIS conjectures and MathOverflow were not done
  systematically (012 joint Dickman, 020 power-free quartics, 026 large gaps, 159/160/167/170/189
  combinatorics, 158 χ(ℝ²) ≥ 6, 107 ω ≤ 9/4 not screened).
- (2) 1337isnot1337/solved-conjectures: only the inventory was skimmed (169 entries, mostly niche).
  plby/lean-proofs was not opened.
- (3) zeta-23: only the fc file and Cl26 §§1, 7 were read.
- The A1 novelty search did not include a MathOverflow site search or Zenodo. The A2 search did
  not read the LeanMeanBean note or Plasma's L65 page in full.

## Lean feasibility summary

| Candidate | Premise location | Port | Effort |
|---|---|---|---|
| A1 Σ tan n/n² | vendored in `conjectures/cookson-hills/Vendor/` (already v4.36.0) | done; needs (2,1) spacing lemma | S |
| A2 Erdős 417 liminf | openai/math `TotientAsymptotic/` (810 files, v4.34.1) | M–L to vendor; S as a hypothesis | S/M |
