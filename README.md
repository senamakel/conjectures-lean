# Robin's inequality under RH in Lean

Robin (*Grandes valeurs de la fonction somme des diviseurs et hypothèse de Riemann*, J. Math.
Pures Appl. 63 (1984)) proved that the Riemann hypothesis is equivalent to
`σ(n) < e^γ n log log n` for every `n > 5040`. Unconditionally the inequality is known for
`5040 < n ≤ 10^{10^{13.11485}}` (Morrill–Platt, Integers 21 (2021), arXiv:1809.10813, extending
Briggs, Experiment. Math. 15 (2006)), for all odd `n > 9` and for all squarefree `n > 30`
(Choie–Lichiardopol–Moree–Solé 2007), and Robin (1984) proved unconditionally the weaker
`σ(n) < e^γ n log log n + 0.6483 n/log log n` for `n ≥ 3`. This repository formalises the
direction RH ⇒ Robin in Lean 4 + Mathlib, with one cited computation as a hypothesis.

## Headline theorems

```lean
-- Robin/Statement.lean (target definitions, unchanged)
def RobinStatement : Prop :=
  ∀ n : ℕ, 5040 < n →
    (σ 1 n : ℝ) < Real.exp Real.eulerMascheroniConstant * n * Real.log (Real.log n)
def LagariasStatement : Prop :=
  ∀ n : ℕ, 1 ≤ n →
    (σ 1 n : ℝ) ≤ (harmonic n : ℝ) + Real.exp (harmonic n) * Real.log (harmonic n)

-- Robin/Small.lean (the cited computation, as a hypothesis)
def RobinVerifiedRange : Prop :=
  ∀ n : ℕ, 5040 < n → Real.log n ≤ Real.exp 30 →
    (σ 1 n : ℝ) < Real.exp Real.eulerMascheroniConstant * n * Real.log (Real.log n)

-- Robin/Main.lean
theorem Robin.robin_of_RH_of_verified (hRH : RiemannHypothesis) (hcomp : RobinVerifiedRange) :
    RobinStatement
-- Robin/Lagarias.lean
theorem Robin.lagarias_of_RH_of_verified (hRH : RiemannHypothesis) (hcomp : RobinVerifiedRange) :
    LagariasStatement
```

## Tier and provenance

| Theorem | Tier | Hypotheses |
|---|---|---|
| `Robin.robin_of_RH_of_verified` | C + H | `RiemannHypothesis`, `RobinVerifiedRange` |
| `Robin.lagarias_of_RH_of_verified` | C + H | `RiemannHypothesis`, `RobinVerifiedRange` |
| `robin_of_verified` (`Unconditional/`) | U + H | `RobinVerifiedRange` |
| `lagarias_of_verified` (`Unconditional/`) | U + H | `RobinVerifiedRange` |

* `RiemannHypothesis` is Mathlib's definition, the one leanprover-community/riemann-hypothesis
  proves as `riemannHypothesis`.
* `RobinVerifiedRange` is Robin's inequality on `5040 < n`, `log n ≤ e^{30}`, i.e.
  `n ≤ exp(e^{30}) < 10^{4.64·10^{12}}`. It is a consequence of Morrill–Platt's Theorem 13
  (`n ≤ 10^{10^{13.11485}}`), which is a large computation over colossally abundant numbers and
  is not replayed here. No theorem in this repository proves it, and none uses `sorry`.
* `RobinStatement` and `LagariasStatement` are not in formal-conjectures; they are the
  statements of Robin (1984) and Lagarias (Amer. Math. Monthly 109 (2002), §3).

## Axioms

From `lake env lean` on a file containing `#print axioms` for each theorem (2026-11-24, this
commit):

```
'Robin.robin_of_RH_of_verified' depends on axioms: [propext, Classical.choice, Quot.sound]
'Robin.lagarias_of_RH_of_verified' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Robin.Lagarias.midCheck_range._native.native_decide.ax_1_1]
```

`Robin.Lagarias.midCheck_range` is one `native_decide`: for each `13 ≤ n ≤ 5040` it computes
`σ(n)` by summing divisors and checks `σ(n) ≤ t + 0.57688 + exp(0.57688)·n·L` over `ℚ`, with
certified rationals `t ≤ log n` and `L ≤ log(t + 0.57688)` (soundness: `ineq_of_midCheck`). The
module builds in about 37 s. `n ≤ 12` is checked by the kernel (`decide +kernel`).

`lake build RobinChecks` pins these lists with `#guard_msgs` and fails if either theorem picks
up another axiom (for example `sorryAx`).

## Proof outline

Full blueprint and constants: [`docs/PLAN.md`](docs/PLAN.md). Put `x = log n`,
`ε = log(1 + 1/x)/log x`, `c_p = −log(1 − 1/p)`.

1. `5040 < n`, `log n ≤ e^{30}`: the hypothesis `RobinVerifiedRange`.
2. Elementary bound (`Robin/Elementary/SigmaBound.lean`):
   `log(σ(n)/n) ≤ ε log n + Σ_{p≤x}(c_p − ε log p) − Σ_{p≤x} min(1/p², ε log p)`.
3. RH input (`Robin/RH/Bach.lean`, `Robin/RH/Psi1.lean`): from erdos-985's weighted explicit
   formula, `|Ψ₁(t) − t²/2| ≤ t^{3/2}/20 + 4t` for `t ≥ 16`, and `|ψ(s) − s| ≤ s^{3/4}` for
   `s ≥ 1000`.
4. Mertens with remainder and Mertens' constant `= γ` (`Robin/Mertens/`).
5. Tail `∫_x^∞ (t − θ) w ≤ (2.4 + 3.3x^{−1/8} + 26x^{−1/4})/(√x log x)` (`Robin/Main/Tail.lean`)
   and gain `≥ (2.67 − 60x^{−1/4})/(√x log x)` (`Robin/Main/Gain/`).
6. For `x ≥ e^{30}`: `1.39r⁴ + 2.4 + 3.3r + 26r² < 2.67 − 60r²` with `r = x^{−1/8} ≤ 1/40`
   (`Robin/Main/Estimate.lean`), so `log(σ(n)/n) < γ + log log x`.
7. Lagarias (`Robin/Lagarias.lean`): Robin plus `H_n ≥ log n + γ` for `n > 5040`; the finite
   check above for `n ≤ 5040`.

## Layout

| File | Content |
|---|---|
| `Robin/Statement.lean` | target statements (do not edit) |
| `Robin/Defs.lean` | `Ψ₁`, `c_p`, `primeSum`, `ε`, gain sum, Mertens weight |
| `Robin/Small.lean` | `RobinVerifiedRange` (the cited range, as a `Prop`) |
| `Robin/Elementary/SigmaBound.lean` | step 2 |
| `Robin/RH/Bach.lean`, `Robin/RH/Psi1.lean` | step 3 |
| `Robin/Mertens/Identity.lean`, `Robin/Mertens/Abelian.lean` (+ subfiles) | step 4 |
| `Robin/Main/Tail.lean`, `Robin/Main/Gain.lean` (+ `Gain/`) | step 5 |
| `Robin/Main/Estimate.lean` | step 6 |
| `Robin/Main.lean` | `robin_of_RH_of_verified` |
| `Robin/Lagarias.lean`, `Robin/Lagarias/{Bounds,Finite}.lean` | step 7 |
| `RobinChecks/Axioms.lean` | `#guard_msgs` axiom allow-list |
| `Unconditional/RobinUnconditional.lean` | RH discharged by riemann-hypothesis |

## Deviations from the literature

* **The range `5040 < n ≤ exp(e^{30})` is a hypothesis.** Robin's own proof covers small `n`
  with Schoenfeld's explicit RH bounds for `θ` and `ψ`, which need zero counting. We use only
  the integrated bound for `Ψ₁` from erdos-985, whose pointwise consequence
  `|ψ(s) − s| ≤ s^{3/4}` costs `x^{−1/8}` and `x^{−1/4}` error terms; those push the analytic
  threshold to `log n ≥ e^{30}`. Below it we rely on Morrill–Platt's computation.
* The proof does not go through colossally abundant numbers; it bounds `σ(n)/n` directly with an
  exponent `ε` that depends on `n`.

## Building

Lean `v4.36.0`, Mathlib `fc4f59e5` (through erdos-985 `9538edb`).

```bash
lake exe cache get
lake build Robin RobinChecks
```

A cold build with the Mathlib cache took 1 min 55 s wall (464 s CPU) on a 95-core machine; the
slowest module is `Robin.Lagarias.Finite` (37 s, the `native_decide`).

## Unconditional version

`Unconditional/RobinUnconditional.lean` imports
[leanprover-community/riemann-hypothesis](https://github.com/leanprover-community/riemann-hypothesis)
(commit `507a75d91d`) and closes the RH hypothesis with its `riemannHypothesis`:

| Theorem | Statement | Axioms |
|---|---|---|
| `robin_of_verified` | `RobinVerifiedRange → RobinStatement` | not yet re-run on this commit |
| `lagarias_of_verified` | `RobinVerifiedRange → LagariasStatement` | not yet re-run on this commit |

There is no `robin_unconditional : RobinStatement` while the range stays a hypothesis.

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

No files are vendored. The weighted explicit formula and the bounds on Euler's constant come
from the lake dependency [erdos-985](https://github.com/senamakel/erdos-985).
