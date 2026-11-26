# Solé–Planat, extremely abundant and extraordinary numbers under RH in Lean

Lean proves three published reformulations of RH, each unconditionally with RH supplied by the
certified proof in
[leanprover-community/riemann-hypothesis](https://github.com/leanprover-community/riemann-hypothesis):

1. **Solé–Planat**: `Ψ(N_n)/(N_n log log N_n) > e^γ/ζ(2)` for every `n ≥ 3`, where
   `Ψ(n) = n ∏_{p ∣ n}(1 + 1/p)` is the Dedekind psi function and `N_n = p_1 ⋯ p_n`.
2. **Nazardonyavi–Yakubovich**: there are infinitely many extremely abundant numbers.
3. **Caveney–Nicolas–Sondow**: `4` is the only extraordinary number.

The main library holds complete Lean proofs of each from RH, through
[nicolas-rh](../nicolas-rh/)'s Nicolas inequality and [robin-rh](../robin-rh/)'s Robin
inequality, and proofs with no RH at all that the two inequalities imply them. Built by OpenHuman
agents.

**Literature status: RH-equivalent**, all three; each is RH in another form.
* P. Solé and M. Planat, *Extreme values of the Dedekind Ψ function*, J. Comb. Number Theory 3
  (2011), no. 1, 1–6, arXiv:1011.1825: the inequality for all `n ≥ 3` is equivalent to RH.
* S. Nazardonyavi and S. Yakubovich, *Extremely abundant numbers and the Riemann hypothesis*,
  J. Integer Seq. 17 (2014), Article 14.2.8, arXiv:1211.2147 (Definition 2.1, Theorem 2.4 in
  arXiv v3): RH holds if and only if there are infinitely many extremely abundant numbers.
* G. Caveney, J.-L. Nicolas and J. Sondow, *Robin's theorem, primes, and a new elementary
  reformulation of the Riemann hypothesis*, Integers 11 (2011), A33, arXiv:1110.5078
  (Definition 1, Theorem 5): RH holds if and only if `4` is the only extraordinary number.

This project proves the direction RH ⇒ statement of each, following the papers' own arguments.

## Headline theorems

```lean
-- Abundant/Statement.lean (target definitions, unchanged)
noncomputable def dedekindPsi (n : ℕ) : ℝ :=
  n * ∏ p ∈ n.primeFactors, (1 + 1 / (p : ℝ))
noncomputable def solePlanatRatio (n : ℕ) : ℝ :=
  dedekindPsi n / (n * Real.log (Real.log n))
def SolePlanatStatement : Prop :=
  ∀ n : ℕ, 3 ≤ n →
    Real.exp Real.eulerMascheroniConstant / (riemannZeta 2).re
      < solePlanatRatio (Nicolas.kthPrimorial n)

noncomputable def robinRatio (n : ℕ) : ℝ :=
  (σ 1 n : ℝ) / (n * Real.log (Real.log n))
def IsExtremelyAbundant (n : ℕ) : Prop :=
  n = 10080 ∨ (10080 < n ∧ ∀ m : ℕ, 10080 ≤ m → m < n → robinRatio m < robinRatio n)
def ExtremelyAbundantInfinite : Prop :=
  {n : ℕ | IsExtremelyAbundant n}.Infinite

def IsExtraordinary (N : ℕ) : Prop :=
  (1 < N ∧ ¬ N.Prime) ∧
    (∀ p : ℕ, p.Prime → p ∣ N → robinRatio (N / p) ≤ robinRatio N) ∧
    (∀ a : ℕ, 1 ≤ a → robinRatio (a * N) ≤ robinRatio N)
def FourOnlyExtraordinary : Prop :=
  ∀ N : ℕ, IsExtraordinary N ↔ N = 4

-- Abundant/SolePlanat.lean, Abundant/Extremely.lean, Abundant/Extraordinary.lean
theorem Abundant.solePlanat_of_nicolas (h : Nicolas.NicolasStatement) : SolePlanatStatement
theorem Abundant.extremelyAbundantInfinite_of_robin_of_nicolas (hR : Robin.RobinStatement)
    (hN : Nicolas.NicolasStatement) : ExtremelyAbundantInfinite
theorem Abundant.fourOnlyExtraordinary_of_robin_of_nicolas (hR : Robin.RobinStatement)
    (hNic : Nicolas.NicolasStatement) : FourOnlyExtraordinary

-- Abundant/RH.lean
theorem Abundant.solePlanat_of_RH (hRH : RiemannHypothesis) : SolePlanatStatement
theorem Abundant.extremelyAbundantInfinite_of_RH (hRH : RiemannHypothesis)
    (hR : Robin.RobinStatement) : ExtremelyAbundantInfinite
theorem Abundant.fourOnlyExtraordinary_of_RH (hRH : RiemannHypothesis)
    (hR : Robin.RobinStatement) : FourOnlyExtraordinary

-- Unconditional/AbundantUnconditional.lean
theorem solePlanat_unconditional : Abundant.SolePlanatStatement
theorem extremelyAbundantInfinite_unconditional : Abundant.ExtremelyAbundantInfinite
theorem fourOnlyExtraordinary_unconditional : Abundant.FourOnlyExtraordinary
```

Two lemmas on the way are useful on their own:

```lean
-- Abundant/Gronwall.lean: Gronwall's lower bound along the multiples of any N, from Nicolas
theorem Abundant.exists_mul_robinRatio_gt (hNic : Nicolas.NicolasStatement) {N : ℕ} (hN : 1 ≤ N)
    {c : ℝ} (hc : c < Real.exp Real.eulerMascheroniConstant) (B : ℕ) :
    ∃ a : ℕ, 1 ≤ a ∧ B ≤ a * N ∧ c < robinRatio (a * N)
-- Abundant/Extraordinary.lean: no N > 5040 has G(N) ≥ G(aN) for every a
theorem Abundant.le_5040_of_forall_mul_le (hR : Robin.RobinStatement)
    (hNic : Nicolas.NicolasStatement) {N : ℕ} (hN : 1 ≤ N)
    (h : ∀ a : ℕ, 1 ≤ a → robinRatio (a * N) ≤ robinRatio N) : N ≤ 5040
```

## Tier and provenance

| Theorem | Tier | Hypotheses |
|---|---|---|
| `Abundant.solePlanat_of_nicolas` | C | `Nicolas.NicolasStatement` |
| `Abundant.extremelyAbundantInfinite_of_robin_of_nicolas` | C | `Robin.RobinStatement`, `Nicolas.NicolasStatement` |
| `Abundant.fourOnlyExtraordinary_of_robin_of_nicolas` | C | `Robin.RobinStatement`, `Nicolas.NicolasStatement` |
| `Abundant.solePlanat_of_RH` | C | `RiemannHypothesis` |
| `Abundant.extremelyAbundantInfinite_of_RH` | C | `RiemannHypothesis`, `Robin.RobinStatement` |
| `Abundant.fourOnlyExtraordinary_of_RH` | C | `RiemannHypothesis`, `Robin.RobinStatement` |
| `solePlanat_unconditional` (`Unconditional/`) | U | none |
| `extremelyAbundantInfinite_unconditional` (`Unconditional/`) | U | none |
| `fourOnlyExtraordinary_unconditional` (`Unconditional/`) | U | none |

* `RiemannHypothesis` is Mathlib's definition, the one leanprover-community/riemann-hypothesis
  proves as `riemannHypothesis`.
* `Nicolas.NicolasStatement` and `Robin.RobinStatement` are the fixed target statements of
  nicolas-rh and robin-rh, imported, not restated. Nicolas' inequality comes from RH inside the
  main library (`Nicolas.nicolas_of_RH`). Robin's inequality is a consequence of RH too
  (`Robin.robin_of_RH`), but that proof needs robin-rh's verified-range sieve, about 54
  core-hours to build; the main library therefore takes `Robin.RobinStatement` as an argument
  and `Unconditional/` supplies it as `Robin.robin_of_RH riemannHypothesis`, the proof of
  robin-rh's `robin_unconditional`.
* The statements are transcribed from the papers (read on arXiv): Solé–Planat's abstract and
  main theorem; Nazardonyavi–Yakubovich's Definition 2.1 and Theorem 2.4 (arXiv v3; the journal
  version numbers them Definition 3 and Theorem 7, not checked against the journal PDF);
  Caveney–Nicolas–Sondow's Definition 1 and Theorem 5. `ζ(2)` is `(riemannZeta 2).re`
  (`riemannZeta_two_re` proves it is `π²/6`). `robinRatio` is the paper's
  `f(n) = G(n) = σ(n)/(n log log n)`; "composite" is `1 < N ∧ ¬ N.Prime`. `N_n` is nicolas-rh's
  `Nicolas.kthPrimorial n`, copied there from formal-conjectures' `Nat.kthPrimorial`.
* formal-conjectures has none of the three (searched at commit `9097e2f` for Dedekind, Solé,
  Planat, extremely abundant, extraordinary, Caveney). Prior formalisations searched:
  formal-conjectures, 1337isnot1337/solved-conjectures, Mathlib (no Dedekind Ψ), and a GitHub
  code search of Lean files (2026-11-26) for `dedekindPsi`, `IsExtremelyAbundant`,
  "extraordinary number" and "Caveney". facebookresearch/atlas-lean (mirrored in
  math-proof/lemma) has definitions of the Dedekind Ψ function and of extremely abundant
  numbers with small `example`s, and no theorem relating either to RH; nothing was found for
  extraordinary numbers.

## Axioms

From `lake env lean` on a file containing `#print axioms` for each theorem (2026-11-26):

```
'Abundant.solePlanat_of_nicolas' depends on axioms: [propext, Classical.choice, Quot.sound]
'Abundant.solePlanat_of_RH' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Nicolas.Check.loop_ok._native.native_decide.ax_1_1]
'Abundant.exists_mul_robinRatio_gt' depends on axioms: [propext, Classical.choice, Quot.sound]
'Abundant.extremelyAbundantInfinite_of_robin_of_nicolas' depends on axioms: [propext, Classical.choice, Quot.sound]
'Abundant.extremelyAbundantInfinite_of_RH' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Nicolas.Check.loop_ok._native.native_decide.ax_1_1]
'Abundant.fourOnlyExtraordinary_of_robin_of_nicolas' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Abundant.Check.check_ok._native.native_decide.ax_1_1]
'Abundant.fourOnlyExtraordinary_of_RH' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Abundant.Check.check_ok._native.native_decide.ax_1_1,
 Nicolas.Check.loop_ok._native.native_decide.ax_1_1]
'Abundant.le_5040_of_forall_mul_le' depends on axioms: [propext, Classical.choice, Quot.sound]
```

* `Nicolas.Check.loop_ok` is nicolas-rh's one `native_decide`, its proved-sound rational
  interval check of Nicolas' inequality at the 9591 primes `3 ≤ p ≤ 10^5`.
* `Abundant.Check.check_ok` is this project's one `native_decide`. For every `n ≤ 5040` it
  certifies in exact rational arithmetic that each of the 4363 composites `4 < n ≤ 5040` has
  `G(n) < e^γ` or `G(n) < G(n/p)` for a prime `p ∣ n` (searched among the prime factors of `n`),
  and that each of the 1259 multiples `8 ≤ 4a ≤ 5040` has `G(4a) < G(4)`. `log log n` is
  bracketed by nicolas-rh's `logUp` (twice) from above and robin-rh's bisection `logLo` (twice)
  from below, each lower value re-checked by `expUpper L ≤ y`; `e^γ ≥ expLower(0.57688)` uses
  erdos-985's `γ > 0.57688`. Soundness: `Abundant.Check.finite_check` and
  `Abundant.Check.four_check` (`Abundant/Check.lean`). The module builds in 92 s wall (71 s user
  CPU, including the `native_decide`) on a loaded 95-core machine. The tightest margins are
  `e^γ − G(420) ≈ 0.00176` (the `γ` bound costs `0.0006` of it) and
  `G(2520) − G(5040) ≈ 0.0136`.

`lake build AbundantChecks` pins the six headline axiom lists with `#guard_msgs` and fails if a
theorem picks up another axiom (for example `sorryAx`).

## Proof outline

Write `f(n) = G(n) = σ(n)/(n log log n)`.

**Solé–Planat** (`Abundant/SolePlanat.lean`).
1. `φ(n) Ψ(n) = n² ∏_{p ∣ n}(1 − p⁻²)` (their Proposition 5), from Mathlib's product formula
   for `φ` (`totient_mul_dedekindPsi`).
2. `∏_{p ∈ s}(1 − p⁻²)⁻¹ ≤ π²/6` for every finite set of primes: Mathlib's Euler product for
   `n ↦ n⁻²` over the `s`-factored numbers, compared with `Σ n⁻² = π²/6`
   (`prod_inv_one_sub_invSq_le`).
3. With `N = N_n ≥ 2^n ≥ 8`, `R(N) = (N/φ(N)) ∏_{p ∣ N}(1 − p⁻²)/log log N > e^γ/ζ(2)` by
   Nicolas' inequality (`solePlanat_of_nicolas`).

**Gronwall along multiples** (`Abundant/Gronwall.lean`, `exists_mul_robinRatio_gt`). For
`N ≥ 1`, `c < e^γ` and `m = N · N_k^e`:
4. `σ(m)/m ≥ σ(N_k^e)/N_k^e` (`σ(n)/n = Σ_{d ∣ n} 1/d` grows along divisibility) and
   `σ(N_k^e)/N_k^e = (N_k/φ(N_k)) ∏_{p ≤ p_k}(1 − p^{−(e+1)}) ≥ (N_k/φ(N_k))/(1 + 8/2^{e+1})`
   (Euler product of `n ↦ n^{−(e+1)}`, dominated by `[n = 1] + (4/2^{e+1}) n⁻²`).
5. `log log m ≤ log(e + 1) + log log N_k` once `N ≤ N_k`. With Nicolas' inequality,
   `f(m) > e^γ L/((1 + 8/2^{e+1})(log(e+1) + L))`, `L = log log N_k ≥ log(k log 2)`. Choose
   `e` with `c(1 + 8/2^{e+1}) < e^γ`, then `k` with `L` large. This replaces Mertens' third
   theorem (not in Mathlib) by Nicolas' inequality.

**Extremely abundant numbers** (`Abundant/Extremely.lean`; the paper's "necessity").
6. If every XA number is `≤ B`, strong induction gives each `n ≥ 10080` an `m ∈ [10080, B]`
   with `f(n) ≤ f(m)` (`exists_le_of_bounded`). Robin puts the maximum of `f` on
   `[10080, B]` below `e^γ`, and step 5 with `N = 1` gives an `n ≥ 10080` above it.

**Extraordinary numbers** (`Abundant/Extraordinary.lean`; the paper's Section 3).
7. Condition (ii) and step 5 give `G(N) ≥ e^γ`; Robin gives `N ≤ 5040`
   (`le_5040_of_forall_mul_le`); for `4 < N ≤ 5040` the finite check contradicts (i) or (ii).
8. `4` is extraordinary: `G(2) < 0 < G(4)`, and `G(4a) < G(4)` by the finite check for
   `4a ≤ 5040` and by Robin (`G(4a) < e^γ < 2 < G(4) ≈ 5.36`) for `4a > 5040`.

## Layout

| File | Content |
|---|---|
| `Abundant/Statement.lean` | target definitions (do not edit) |
| `Abundant/SolePlanat.lean` | steps 1–3 |
| `Abundant/Gronwall.lean` | steps 4–5 |
| `Abundant/Extremely.lean` | step 6 |
| `Abundant/Check.lean` | the checker for `n ≤ 5040`, its soundness and the `native_decide` |
| `Abundant/Extraordinary.lean` | steps 7–8 |
| `Abundant/RH.lean` | the RH-hypothesis forms, through `Nicolas.nicolas_of_RH` |
| `AbundantChecks/Axioms.lean` | `#guard_msgs` axiom allow-list |
| `Unconditional/AbundantUnconditional.lean` | RH discharged by riemann-hypothesis |

## Deviations from the literature

* None in the statements: each is the paper's, with the paper's range.
* Gronwall's theorem enters only as its lower half (`limsup f ≥ e^γ`, along multiples of any
  `N`), proved here from Nicolas' inequality instead of from Mertens' third theorem. So the
  main-library theorems take Nicolas' inequality (or RH) as well as Robin's.
* Caveney–Nicolas–Sondow show that `4` is extraordinary with Robin's unconditional bound
  `G(n) < e^γ + 0.6483/(log log n)²`, which is not in Lean; here it follows from Robin's
  inequality for `4a > 5040` and from the finite check for `4a ≤ 5040`. Their Lemma 2 checks
  only the 23 composites `r ≤ 5040` with `G(r) ≥ e^γ`; the check here also certifies
  `G(n) < e^γ` for every other composite `n ≤ 5040`.

## Building

Lean `v4.36.0`, Mathlib `fc4f59e5`. Requires [nicolas-rh](../nicolas-rh/) and
[robin-rh](../robin-rh/) by path (erdos-985 through them). Only the light robin-rh modules that
nicolas-rh's `Nicolas.Main` imports are built (`Robin.Defs`, `Robin.Lagarias.Bounds`,
`Robin.Mertens.*`, `Robin.RH.*`, `Robin.Main.Tail`, `Robin.Statement`); robin-rh's
verified-range sieve is not.

```bash
lake build Abundant AbundantChecks
```

From a cold nicolas-rh and robin-rh (erdos-985 and Mathlib built), building through
`Nicolas.Main` took 2 min 20 s wall (122 s user CPU) on a loaded 95-core machine. The slowest
`Abundant` module is `Abundant.Check` (92 s, the `native_decide`); the others take under 30 s.

## Unconditional version

`Unconditional/AbundantUnconditional.lean` imports
[leanprover-community/riemann-hypothesis](https://github.com/leanprover-community/riemann-hypothesis)
(commit `507a75d91d`) and closes the RH hypothesis with its `riemannHypothesis`, and Robin's
inequality with `Robin.robin_of_RH riemannHypothesis`:

| Theorem | Statement | Axioms (real output, 2026-11-26) |
|---|---|---|
| `solePlanat_unconditional` | `SolePlanatStatement` | standard three + `Nicolas.Check.loop_ok` (1 `native_decide`) |
| `extremelyAbundantInfinite_unconditional` | `ExtremelyAbundantInfinite` | standard three + `Nicolas.Check.loop_ok` + robin-rh's 624 `native_decide`s (`RobinCompute.small_ok`, `RobinCompute.chunk_0` to `chunk_622`) |
| `fourOnlyExtraordinary_unconditional` | `FourOnlyExtraordinary` | standard three + `Abundant.Check.check_ok` + `Nicolas.Check.loop_ok` + robin-rh's 624 `native_decide`s (same list) |

```bash
scripts/check-unconditional.sh /path/to/riemann-hypothesis   # cloned there if missing
```

The script builds `Abundant` and robin-rh's full `Robin` library, whose verified-range sieve
takes about 54 core-hours unless its build output is already present. It uses
riemann-hypothesis's community cache, about 93 GB. The import opens around 900,000 module files
and needs about 19 GB of RAM. Raise the open-file limit first; on Linux
`sudo prlimit --pid $$ --nofile=2000000:2000000`, on macOS
`sudo sysctl -w kern.maxfiles=2000000 kern.maxfilesperproc=1500000 kern.maxvnodes=1500000`.

Checked 2026-11-26 at monorepo commit `8ce94d1`: robin-rh's full `Robin` library was built (its
verified-range sieve was replayed from an existing build of byte-identical sources, so the 54
core-hours were not repeated here), then `lean Unconditional/AbundantUnconditional.lean` ran
against riemann-hypothesis `507a75d91d` (2430 s wall including a wait for the single RH-import
slot). No `sorryAx`. Real output, with the 623 lines `RobinCompute.chunk_0._native.native_decide.ax_1_1`
to `RobinCompute.chunk_622._native.native_decide.ax_1_1` (each present exactly once) folded into
one line:

```
'solePlanat_unconditional' depends on axioms: [propext, Classical.choice, Quot.sound,
 Nicolas.Check.loop_ok._native.native_decide.ax_1_1]
'extremelyAbundantInfinite_unconditional' depends on axioms: [propext, Classical.choice, Quot.sound,
 RobinCompute.small_ok._native.native_decide.ax_1_1,
 Nicolas.Check.loop_ok._native.native_decide.ax_1_1,
 RobinCompute.chunk_{0..622}._native.native_decide.ax_1_1  (623 axioms)]
'fourOnlyExtraordinary_unconditional' depends on axioms: [propext, Classical.choice, Quot.sound,
 RobinCompute.small_ok._native.native_decide.ax_1_1,
 Abundant.Check.check_ok._native.native_decide.ax_1_1,
 Nicolas.Check.loop_ok._native.native_decide.ax_1_1,
 RobinCompute.chunk_{0..622}._native.native_decide.ax_1_1  (623 axioms)]
```

The riemann-hypothesis proof adds no axioms of its own. It was certified by the Lean FRO and the Mathlib Initiative on 2026-11-21, and independent kernels accept it (math.mit.edu/~drew/grh). This check links against the community build cache and does not repeat those kernel checks.

## Credits

No files are vendored. `kthPrimorial` and `NicolasStatement` come from the lake dependency
[nicolas-rh](../nicolas-rh/) (`kthPrimorial` is copied there from
[formal-conjectures](https://github.com/google-deepmind/formal-conjectures), Apache-2.0);
`RobinStatement`, `expUpper`, `expLower` and `logLo` from [robin-rh](../robin-rh/); `logUp`
from nicolas-rh; the bound `γ > 0.57688` from [erdos-985](../erdos-985/).
