# Robin's inequality from RH in Lean

**Literature status: RH-equivalent.** Robin (*Grandes valeurs de la fonction somme des
diviseurs et hypothèse de Riemann*, J. Math. Pures Appl. 63 (1984)) proved that the Riemann
hypothesis is equivalent to `σ(n) < e^γ n log log n` for every `n > 5040`; Lagarias (Amer. Math.
Monthly 109 (2002)) gave the equivalent form `σ(n) ≤ H_n + exp(H_n) log H_n`. This repository is a
Lean 4 + Mathlib proof that RH implies Robin's inequality, following Robin (1984), and that RH
implies Lagarias's form. Robin's inequality is equivalent to RH, so the unconditional theorem in
`Unconditional/` says nothing beyond the RH claim. Unconditionally the inequality is known for
`5040 < n ≤ 10^{10^{13.11485}}` (Morrill–Platt, Integers 21 (2021), extending Briggs, Experiment.
Math. 15 (2006)), for odd `n > 9` and squarefree `n > 30` (Choie–Lichiardopol–Moree–Solé 2007),
and Robin proved `σ(n) < e^γ n log log n + 0.6483 n/log log n` for `n ≥ 3`.

## Headline theorems

```lean
-- Robin/Statement.lean (target definitions, unchanged)
def RobinStatement : Prop :=
  ∀ n : ℕ, 5040 < n →
    (σ 1 n : ℝ) < Real.exp Real.eulerMascheroniConstant * n * Real.log (Real.log n)
def LagariasStatement : Prop :=
  ∀ n : ℕ, 1 ≤ n →
    (σ 1 n : ℝ) ≤ (harmonic n : ℝ) + Real.exp (harmonic n) * Real.log (harmonic n)

-- Robin/Small.lean
def RobinVerifiedRange : Prop :=
  ∀ n : ℕ, 5040 < n → Real.log n ≤ Real.exp 30 →
    (σ 1 n : ℝ) < Real.exp Real.eulerMascheroniConstant * n * Real.log (Real.log n)

-- Robin/Verified.lean
theorem Robin.robin_verified_range : RobinVerifiedRange
theorem Robin.robin_of_RH (hRH : RiemannHypothesis) : RobinStatement
theorem Robin.lagarias_of_RH (hRH : RiemannHypothesis) : LagariasStatement

-- Robin/Main.lean, Robin/Lagarias.lean (the analytic part alone)
theorem Robin.robin_of_RH_of_verified (hRH : RiemannHypothesis) (hcomp : RobinVerifiedRange) :
    RobinStatement
theorem Robin.lagarias_of_RH_of_verified (hRH : RiemannHypothesis) (hcomp : RobinVerifiedRange) :
    LagariasStatement
```

## Tier and provenance

| Theorem | Tier | Hypotheses |
|---|---|---|
| `Robin.robin_verified_range` | D | none (a finite computation, `native_decide`) |
| `Robin.robin_of_RH` | C | `RiemannHypothesis` |
| `Robin.lagarias_of_RH` | C | `RiemannHypothesis` |
| `Robin.robin_of_RH_of_verified`, `Robin.lagarias_of_RH_of_verified` | C + H | `RiemannHypothesis`, `RobinVerifiedRange` |
| `robin_unconditional`, `lagarias_unconditional` (`Unconditional/`) | U | none |

* `RiemannHypothesis` is Mathlib's definition, the one leanprover-community/riemann-hypothesis
  proves as `riemannHypothesis`.
* `RobinVerifiedRange` is Robin's inequality for `5040 < n`, `log n ≤ e^{30}`. It used to be a
  cited hypothesis (Morrill–Platt); it is now proved in Lean by the computation in
  `Robin/Compute/` and `RobinCompute/`.
* `RobinStatement` and `LagariasStatement` are not in formal-conjectures.

## Axioms

AXIOMS_BLOCK

## Proof outline

Full blueprint and constants: [`docs/PLAN.md`](docs/PLAN.md). Put `x = log n`.

1. **Analytic range `x ≥ e^{30}`** (`Robin/Main.lean`), unchanged: with
   `ε = log(1+1/x)/log x`, `log(σ(n)/n) ≤ ε log n + Σ_{p≤x}(c_p − ε log p) − Σ_{p≤x} min(1/p², ε log p)`
   (`Robin/Elementary/SigmaBound.lean`); the RH bound `|Ψ₁(t) − t²/2| ≤ t^{3/2}/20 + 4t`
   (`Robin/RH/`, from erdos-985's explicit formula); Mertens with remainder (`Robin/Mertens/`);
   tail `≤ (2.4 + 3.3x^{−1/8} + 26x^{−1/4})/(√x log x)` and gain `≥ (2.67 − 60x^{−1/4})/(√x log x)`
   (`Robin/Main/`); for `r = x^{−1/8} ≤ 1/40`, `1.39r⁴ + 2.4 + 3.3r + 26r² < 2.67 − 60r²`.
2. **Finite range `5040 < n`, `x ≤ e^{30}`** (`Robin/Compute/`, `RobinCompute/`):
   * Envelope (`Envelope.lean`): for every `ε > 0` and `n ≥ 1`,
     `log(σ(n)/n) ≤ ε log n + Σ_p max_k (log(σ(p^k)/p^k) − kε log p)`, the bound that defines
     colossally abundant numbers. With `log(σ(p^k)/p^k) = Σ_{j<k} log(1 + 1/a_j)`,
     `a_j = p + ⋯ + p^{j+1}`, primes `p ≥ B` contribute nothing when `log(1+1/B) ≤ ε log B`,
     and each `p < B` contributes `log(1+1/p) − ε log p` plus prime-power extras for `p < Q`.
   * Line test: the envelope is a line `εx + C` in `x = log n`; `log log x` is concave, so
     `εx + C < γ + log log x` at both ends of `[lo, hi]` gives it on all of `[lo, hi]`, hence
     Robin's inequality for every `n` with `log n ∈ [lo, hi]`.
   * The computation streams over `m < 1.0703·10^{13}` with a segmented sieve, accumulating
     an upper bound for `Σ log(1 + 1/p)` and a lower bound for `Σ log p` over the unmarked
     numbers (a superset of the primes; a marked number is a proper multiple, so the sieve
     needs no completeness proof). Above `2^{26}` each segment of length `h ≤ 2^{22}` is
     summarised by its count, `Σi` and `Σi²`, using `2/(2m+1) ≤ (2/b)(1 − t + t²)` and
     `log(1+t) ≥ t − t²/2`. At about CK_COUNT checkpoints (spacing `2^{⌊(3/4)log₂ B⌋}`) it picks
     `ε`, computes the extras and extends the covered interval of `x`.
   * All logarithms are fixed-point (`D = 2^{96}`) partial sums of Mathlib's
     `log(1 + 1/a) = Σ 2/(2k+1)·(2a+1)^{−2k−1}`, with the geometric tail for upper bounds
     (`Log.lean`). Euler's constant: `γ ≥ H_N − log N − 1/(2N)` with `N = 2^{20}` (the
     trapezoid rule makes this sequence increasing), giving `γ > 0.5772156649014`.
   * `5040 < n ≤ 10000` is checked directly (`σ(n)` by trial division, certified logs).
   * `Robin/Compute/Range.lean` assembles `RobinVerifiedRange`: the final covered interval
     reaches `x = FINAL_COV > e^{30} ≈ 1.0686·10^{13}`.
3. **Lagarias** (`Robin/Lagarias.lean`): Robin plus `H_n ≥ log n + γ` for `n > 5040`; one
   `native_decide` over `ℚ` for `13 ≤ n ≤ 5040`, `decide +kernel` for `n ≤ 12`.

## Layout

| File | Content |
|---|---|
| `Robin/Statement.lean` | target statements (do not edit) |
| `Robin/Defs.lean`, `Robin/Elementary/SigmaBound.lean` | definitions; the elementary bound |
| `Robin/RH/`, `Robin/Mertens/`, `Robin/Main/` | the analytic range `x ≥ e^{30}` under RH |
| `Robin/Main.lean` | `robin_of_RH_of_verified` |
| `Robin/Small.lean` | `RobinVerifiedRange` (the statement of the finite range) |
| `RobinCompute/Core.lean` | the executable checker (Lean core only, `precompileModules`) |
| `RobinCompute/Data.lean` | the 624 chunk boundary states (generated) |
| `Robin/Compute/Log.lean` | fixed-point logarithms and `γ`: soundness |
| `Robin/Compute/Envelope.lean` | the envelope, monotonicity, concavity line test |
| `Robin/Compute/Sieve.lean` | sieve and scan soundness |
| `Robin/Compute/Step.lean`, `Checkpoint.lean`, `Run.lean` | the invariant `Valid` and its preservation; direct check |
| `Robin/Compute/Chunks/C000–C622.lean`, `Small.lean` | the `native_decide` checks (generated) |
| `Robin/Compute/Chain.lean`, `Range.lean` | chaining the chunks; `RobinVerifiedRange` |
| `Robin/Verified.lean` | `robin_verified_range`, `robin_of_RH`, `lagarias_of_RH` |
| `Robin/Lagarias.lean`, `Robin/Lagarias/` | Lagarias's form |
| `RobinChecks/Axioms.lean` | axiom allow-list |
| `Unconditional/RobinUnconditional.lean` | RH supplied by riemann-hypothesis |

## Deviations from the literature

* Robin covers small `n` with Schoenfeld's explicit RH bounds. We have only the integrated bound
  for `Ψ₁` from erdos-985, whose pointwise consequence `|ψ(s) − s| ≤ s^{3/4}` costs
  `x^{−1/8}` and `x^{−1/4}` error terms and pushes the analytic threshold to `x ≥ e^{30}`. The
  whole range below it is a computation, about `π(1.07·10^{13}) ≈ 3.6·10^{11}` primes; we
  replay it in Lean instead of citing Morrill–Platt.
* The analytic part bounds `σ(n)/n` directly with an `n`-dependent exponent instead of going
  through colossally abundant numbers; the computation uses the colossally-abundant envelope.

## Building

Lean `v4.36.0`, Mathlib `fc4f59e5` (through erdos-985 `9538edb`).

```bash
lake exe cache get
lake build Robin RobinChecks
```

BUILD_TIMES

`RobinCompute` is a core-only library with `precompileModules = true`, so `native_decide`
runs it as native code (the interpreter is about 75× slower). To regenerate the chunk states,
run the same code as an executable over the chunks and write `RobinCompute/Data.lean`; the
scripts used are described in `docs/PLAN.md`.

## Unconditional version

`Unconditional/RobinUnconditional.lean` imports
[leanprover-community/riemann-hypothesis](https://github.com/leanprover-community/riemann-hypothesis)
(commit `507a75d91d`) and closes the RH hypothesis with its `riemannHypothesis`. It gives Robin's
and Lagarias's inequalities, given the Lean proof of RH in leanprover-community/riemann-hypothesis,
which has not been independently verified. Since both are equivalent to RH, this says nothing
beyond the RH claim.

UNCOND_TABLE

```bash
scripts/check-unconditional.sh /path/to/riemann-hypothesis   # cloned there if missing
```

The script uses that project's community cache, about 93 GB. The import opens around 900,000
module files and needs about 19 GB of RAM. Raise the open-file limit first; on Linux
`sudo prlimit --pid $$ --nofile=2000000:2000000`, on macOS
`sudo sysctl -w kern.maxfiles=2000000 kern.maxfilesperproc=1500000 kern.maxvnodes=1500000`.

The riemann-hypothesis proof adds no axioms of its own. The cache contains outputs of untrusted
builds, so this links the proofs but does not re-verify the RH/GRH proof, whose independent
verification is still pending.

## Credits

No files are vendored. The weighted explicit formula and the bounds on Euler's constant used by
the analytic part come from the lake dependency [erdos-985](https://github.com/senamakel/erdos-985).
