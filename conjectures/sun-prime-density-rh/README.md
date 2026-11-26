# Sun's conjecture on π(n^k)/n^k for every k ≥ 4 under RH in Lean

Zhi-Wei Sun conjectured (OEIS [A038098](https://oeis.org/A038098), comment of 17 October 2015;
MathOverflow [301662](https://mathoverflow.net/questions/301662), 2018) that for every integer
`k > 2` the sequence `π(n^k)/n^k` (`n = 2, 3, …`) is strictly decreasing. This repository proves
in Lean that RH implies the conjecture for **every exponent `k ≥ 4` and every `n ≥ 2`**, and for
`k = 3` outside the range `141 ≤ n < 10⁷`. Under RH, Sun's whole conjecture is therefore
equivalent to its case `k = 3`, `141 ≤ n < 10⁷` (`sunConjecture_iff_of_RH`). With RH supplied by
the Lean proof in
[leanprover-community/riemann-hypothesis](https://github.com/leanprover-community/riemann-hypothesis),
`Unconditional/` states the same results with no hypothesis.

**Literature status: RH-consequence.** The statement is Sun's 2015 conjecture, formalised in
formal-conjectures as `OeisA38098.conjecture1` with category `research open`. We did not find a
proof, conditional or not, of any instance `k ≥ 3` in the literature (searched 2026-11-26; list
below). On MathOverflow Sun wrote "Even RH (Riemann Hypothesis) might not be helpful to my
question" (about `k = 2`); the only attempt posted there, with Dusart's unconditional bounds,
fails. The deduction here uses Schoenfeld's explicit RH bound for `π(x) − li(x)` (Schoenfeld
1976, Corollary 1, proved from RH in [`schoenfeld-rh`](../schoenfeld-rh/)) and an exact or
analytic check of 565 pairs below `n^k = 10¹⁰`. The proof of RH used in `Unconditional/` is
L. Alpöge's (2026), certified by the Lean FRO and the Mathlib Initiative on 2026-11-21.

```lean
-- SunPrimeDensity/Main.lean
theorem SunPrimeDensity.sun_of_RH (hRH : RiemannHypothesis) (k : ℕ) (hk : 4 ≤ k) (n : ℕ)
    (hn : 2 ≤ n) :
    (Nat.primeCounting ((n + 1) ^ k) : ℚ) / ((n + 1) ^ k : ℚ) <
    (Nat.primeCounting (n ^ k) : ℚ) / (n ^ k : ℚ)
theorem SunPrimeDensity.sunConjectureFrom_four_of_RH (hRH : RiemannHypothesis) :
    SunConjectureFrom 4
theorem SunPrimeDensity.sunConjectureFrom_four_of_schoenfeld (hS : Schoenfeld.SchoenfeldPi) :
    SunConjectureFrom 4
theorem SunPrimeDensity.sun_three_of_RH (hRH : RiemannHypothesis) (n : ℕ) (hn : 2 ≤ n)
    (hrange : n ≤ 140 ∨ 10 ^ 7 ≤ n) :
    (Nat.primeCounting ((n + 1) ^ 3) : ℚ) / ((n + 1) ^ 3 : ℚ) <
    (Nat.primeCounting (n ^ 3) : ℚ) / (n ^ 3 : ℚ)
theorem SunPrimeDensity.sunConjecture_iff_of_RH (hRH : RiemannHypothesis) :
    SunConjecture ↔ ∀ n : ℕ, 141 ≤ n → n < 10 ^ 7 →
      (Nat.primeCounting ((n + 1) ^ 3) : ℚ) / ((n + 1) ^ 3 : ℚ) <
      (Nat.primeCounting (n ^ 3) : ℚ) / (n ^ 3 : ℚ)

-- Unconditional/SunPrimeDensityUnconditional.lean
theorem sun_unconditional (k : ℕ) (hk : 4 ≤ k) (n : ℕ) (hn : 2 ≤ n) :
    (Nat.primeCounting ((n + 1) ^ k) : ℚ) / ((n + 1) ^ k : ℚ) <
    (Nat.primeCounting (n ^ k) : ℚ) / (n ^ k : ℚ) :=
  SunPrimeDensity.sun_of_RH riemannHypothesis k hk n hn
```

The targets (`SunPrimeDensity/Statement.lean`):

```lean
def SunConjecture : Prop :=
  ∀ (k : ℕ) (_hk : 2 < k) (n : ℕ) (_hn : 2 ≤ n),
    (Nat.primeCounting ((n + 1) ^ k) : ℚ) / ((n + 1) ^ k : ℚ) <
    (Nat.primeCounting (n ^ k) : ℚ) / (n ^ k : ℚ)
def SunConjectureFrom (k₀ : ℕ) : Prop :=
  ∀ (k : ℕ) (_hk : k₀ ≤ k) (n : ℕ) (_hn : 2 ≤ n),
    (Nat.primeCounting ((n + 1) ^ k) : ℚ) / ((n + 1) ^ k : ℚ) <
    (Nat.primeCounting (n ^ k) : ℚ) / (n ^ k : ℚ)
def SunConjectureSquares : Prop := … -- conjecture (ii), k = 2; not proved
```

## Tier and provenance

| Theorem | Tier | Hypotheses |
|---|---|---|
| `sun_unconditional`, `sunConjectureFrom_four` (`Unconditional/`) | U | none |
| `sun_three_unconditional`, `sunConjecture_iff_three_range` (`Unconditional/`) | U | none |
| `sun_of_RH`, `sunConjectureFrom_four_of_RH` | C | RH |
| `sun_three_of_RH`, `sunConjecture_iff_of_RH`, `sunConjecture_of_RH_of_three` | C | RH |
| `sunConjectureFrom_four_of_schoenfeld` | C | `SchoenfeldPi` (Schoenfeld's π bound) |
| `tail`, `tail_three`, `Check.finite_range` | C | `SchoenfeldPi` |
| `pi_mid_explicit` | D | none (PsiCert and `ThetaSmallRange`, both theorems of schoenfeld-rh) |

* `SunConjecture` is `OeisA38098.conjecture1` of
  [formal-conjectures](https://github.com/google-deepmind/formal-conjectures)
  (`FormalConjectures/OEIS/38098.lean`, commit `9097e2f`), statement body copied word for word;
  `SunConjectureSquares` is `conjecture2` of the same file.
* `RiemannHypothesis` is Mathlib's. `SchoenfeldPi` is schoenfeld-rh's
  `PiBound (1 / (8 * π)) 2657`, `|π(⌊x⌋) − li(x)| < √x log x/(8π)` for real `x ≥ 2657`, with
  `li = Real.logIntegral` the principal value (formal-conjectures' definition,
  `li(x) = li(2) + ∫₂ˣ dt/log t`); `schoenfeldPi_of_RH` proves it from RH.

## Axioms

`#print axioms` (`scripts/axioms.lean`, 2026-11-26):

```
'SunPrimeDensity.sun_of_RH' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Schoenfeld.Check.checkA_psiCert._native.native_decide.ax_1_1,
 Schoenfeld.Check.checkA_theta._native.native_decide.ax_1_1,
 Schoenfeld.Check.checkB_pi._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk00._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk01._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk02._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk03._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk04._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk05._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk06._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk07._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk08._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk09._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk10._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk11._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk12._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk13._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk14._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk15._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk16._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk17._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk18._native.native_decide.ax_1_1,
 Schoenfeld.PsiCert.chunk19._native.native_decide.ax_1_1,
 SunPrimeDensity.Check.allOK_eq_true._native.native_decide.ax_1_1,
 SunPrimeDensity.Check.chainOK_piTable._native.native_decide.ax_1_1]
'SunPrimeDensity.tail' depends on axioms: [propext, Classical.choice, Quot.sound]
'SunPrimeDensity.tail_three' depends on axioms: [propext, Classical.choice, Quot.sound]
'SunPrimeDensity.pi_mid_explicit' depends on axioms: [propext, Classical.choice, Quot.sound]
```

`sunConjectureFrom_four_of_RH` has the same list. `sun_three_of_RH` and
`sunConjecture_iff_of_RH` have the same list with `allOK3_eq_true` in place of `allOK_eq_true`
(and the latter has both). Beyond the standard three:

* 23 `native_decide` from schoenfeld-rh: PsiCert (`checkA_psiCert` and 20 chunks, an exact
  segmented sieve for `ψ` up to `10¹⁰`), `checkA_theta` (`ThetaSmallRange`) and `checkB_pi`
  (`PiSmallRange`). See the schoenfeld-rh README for their checkers and soundness proofs.
* 3 here, each a proved-sound checker (`SunPrimeDensity/Check.lean`):
  * `chainOK_piTable`: recounts the primes up to `41⁴ = 2825761` by trial division
    (schoenfeld-rh's `cntLoop`, soundness `cntLoop_eq`) and checks the 204 values of `piTable`
    (`chainOK_sound`). 32 s.
  * `allOK_eq_true`: the 565 pairs `k ≥ 4`, `n ≥ 2`, `n^k < 10¹⁰` (soundness
    `exactOK_sound`, `pairOK_sound`, `finite_range`). 0.9 s.
  * `allOK3_eq_true`: `k = 3`, `2 ≤ n ≤ 140`, exactly from the table (`three_small`). Under 1 s.

## Proof outline

Write `x = n^k`, `y = (n+1)^k` and `D(x) = li(x) − x/log x`.

1. **Comparison** (`Analytic.lean`, `ratio_lt_of_bounds`). Since
   `li(y) − li(x) ≤ (y − x)/log x`, `li(x)/x − li(y)/y ≥ (1 − x/y) D(x)/x`. So if
   `|π(x) − li(x)| ≤ E_x`, `|π(y) − li(y)| ≤ E_y` and
   `(1 − x/y) D(x)/x > E_x/x + E_y/y`, then `π(y)/y < π(x)/x`. Integration by parts gives
   `D(x) ≥ (x − 2)/log² x − 2.886` (`logIntegral_sub_ge`).
2. **Tail, `n^k ≥ 10¹⁰`, every `k ≥ 4`** (`Tail.lean`). Bernoulli gives
   `1 − x/y ≥ k/(n+k) ≥ 4/(n+4) ≥ 4/(x^{1/4} + 4)`, uniformly in `k`. With Schoenfeld's
   `E(t) = √t log t/(8π)`, `E(y)/y ≤ E(x)/x`, and it is enough that
   `2E(x)(x^{1/4} + 4) < 4((x − 2)/log² x − 2.886)`, an inequality in `x` alone. With
   `w = x^{1/32}` and `log w ≤ w/e`, it becomes a polynomial inequality, true for `w ≥ 2.053`;
   at `x = 10¹⁰` the margin is 11 %.
3. **Finite range, `n^k < 10¹⁰`** (`Check.lean`): 565 pairs (`k ≤ 33`, `n ≤ 316`).
   * 83 pairs with `(n+1)^k ≤ 41⁴` exactly (all of `k = 4, n ≤ 40`; `k = 5, n ≤ 18`; down to
     `k = 13, n = 2`; this includes every pair with `n^k < 2657`).
   * 482 pairs by step 1 with rational enclosures: `E(t)` is `piErrMid t =
     3.9252 √t/log t + 49.886 + 3.9252 · (10.15/6.15) · 2√t/log² t` on `[4·10⁵, 10¹⁰]`
     (`pi_mid_explicit`: the bound inside schoenfeld-rh's `pi_mid`, from PsiCert, kept as a
     function of `t`; about 2.5 times smaller than Schoenfeld's at `t = 3·10⁸`), and Schoenfeld's
     bound elsewhere. The smallest ratio of the two sides is 1.022, at `(k, n) = (4, 41)`.
4. **`k = 3`** (`Tail3.lean`, `Check.three_small`). The argument of step 2 with
   `1 − x/y ≥ 3/(n+3)` and `w = n^{1/16}` works for `n ≥ 10⁷` (polynomial inequality for
   `w ≥ 2.738`, margin 5 %); exact counts give `n ≤ 140`.

## Layout

| File | Content |
|---|---|
| `SunPrimeDensity/Statement.lean` | `SunConjecture`, `SunConjectureFrom`, `SunConjectureSquares` |
| `SunPrimeDensity/Analytic.lean` | the comparison, the bound for `D(x)`, `pi_mid_explicit`, monotonicity of `log t/√t` |
| `SunPrimeDensity/Tail.lean` | `tail_core`, `tail` (`k ≥ 4`, `n^k ≥ 10¹⁰`) |
| `SunPrimeDensity/Tail3.lean` | `tail3_core`, `tail_three` (`k = 3`, `n ≥ 10⁷`) |
| `SunPrimeDensity/Check.lean` | `piTable`, `chainOK`, `exactOK`, `sqrtUp`, `EQ`, `pairOK`, `allOK`, `allOK3` and their soundness |
| `SunPrimeDensity/Main.lean` | `sun_of_RH`, `sun_three_of_RH`, `sunConjecture_iff_of_RH` |
| `Unconditional/SunPrimeDensityUnconditional.lean` | RH discharged |

## What stays open, and why

* **`k = 3`, `141 ≤ n < 10⁷`.** The two terms differ by about `1/(3n log² n)`; Schoenfeld's error
  term is about `log n/(8π n^{3/2})` per term. The sufficient condition of step 1 with
  Schoenfeld's bound first holds for all larger `n` at `n = 8441233` (crude `D`) or about
  `7.33·10⁶` (with `D ≈ x/log² x + 2x/log³ x`). The PsiCert bound reaches only `x = 10¹⁰`
  (`n ≤ 2154`) and does not separate any `k = 3` pair with `14 ≤ n ≤ 2155`. Closing the range
  needs `π(n³)` to `x ≈ 10²¹`, or an explicit `|π(x) − li(x)|` bound of Büthe's strength
  (`≈ √x/log x`) up to `10²¹`, which is not in Lean. Exact counts are cheap only to about
  `10⁹`.
* **Conjecture (ii), `k = 2`** (`SunConjectureSquares`) is out of reach of RH: the step is
  about `1/(2n log² n)` while the RH error per term is about `log n/(4πn)`; the ratio of the
  two tends to 0 (0.011 at `n = 10³`, 0.0004 at `n = 10⁹`). It is a Legendre-strength
  statement.

## Deviations from the literature

None in the statement. The constant `2.886 = 2/log 2` bounds `|2/log 2 − li(2)|` crudely
(`0 ≤ li(2) ≤ 2`); a sharper value is not needed.

## Building

Lean `v4.36.0`, Mathlib `fc4f59e5`. `lake build` (default target `SunPrimeDensity`); it requires
`../erdos-985` and `../schoenfeld-rh` by path and reuses their build. Own modules: about
3 minutes in total (`Check` 67 s, of which 32 s is `chainOK_piTable`). Building schoenfeld-rh
from scratch costs CPU-hours (PsiCert).

## Unconditional version

| Theorem | Statement | Axioms |
|---|---|---|
| `sun_unconditional` | `π((n+1)^k)/(n+1)^k < π(n^k)/n^k` for `k ≥ 4`, `n ≥ 2` | standard three + the 25 `native_decide` above |
| `sunConjectureFrom_four` | `SunConjectureFrom 4` | the same |
| `sun_three_unconditional` | `k = 3`, `n ≤ 140` or `n ≥ 10⁷` | the same with `allOK3` |
| `sunConjecture_iff_three_range` | `SunConjecture` ⇔ `k = 3` for `141 ≤ n < 10⁷` | all 26 |

riemann-hypothesis commit `507a75d91d`. Check with `scripts/check-unconditional.sh`; it needs
about 93 GB of cache, 19 GB of RAM and an open-file limit near 900k (on Linux:
`sudo prlimit --pid $$ --nofile=2000000:2000000`). **Not run yet** for this repository.

The riemann-hypothesis proof adds no axioms of its own. The cache contains outputs of untrusted
builds, so this links the proofs but does not re-verify the RH/GRH proof, whose independent
verification is still pending.

## Novelty search (2026-11-26)

No proof of any instance `k ≥ 3`, conditional or not, was found in:

* the OEIS A038098 page (Sun's comment of 17 Oct 2015; no later comment on a proof);
* MathOverflow 301662 (2018): comments by Paseman, Schlage-Puchta (pairwise distinctness for
  `k = 2` in restricted ranges under RH), kodlu; one answer, a failed attempt with Dusart's
  bounds;
* arXiv and the web (Exa search: Sun's slides, his arXiv:1402.6641 and 1208.2683 problem lists,
  Wang–Zhu arXiv:1303.5595 on other monotonicity conjectures of Sun; nothing on `π(n^k)/n^k`);
* formal-conjectures pull requests (`gh pr list --state all --search A038098`, `--search 38098`:
  none);
* GitHub code search (`OeisA38098`, `A038098`): statement mirrors only (mathdb-lean/problems,
  competemath/emissary-archangel, epoch-research/LeanOpenProblems). The run
  `epoch-research/LeanOpenProblems-results`, `oeis_38098_conjecture_0`, submitted a proof using
  `sorryAx` and was scored incorrect;
* 1337isnot1337/solved-conjectures (local clone: no `38098` hit in a Lean file).

## Credits

No files are vendored. Schoenfeld's bound, PsiCert, the rational enclosures `logLo`, `logUp`,
`sqrtLo`, `invUp`, `invLo` and the prime counter `cntLoop` come from the `schoenfeld-rh` lake
dependency. The statements are copied from formal-conjectures (Apache-2.0, commit `9097e2f`);
see `NOTICE`. Built by OpenHuman agents.
