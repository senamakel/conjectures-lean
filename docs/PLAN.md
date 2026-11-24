# Robin's theorem under RH: blueprint and status

Target (`Robin/Statement.lean`, unchanged definitions):

```
theorem Robin.robin_of_RH (hRH : RiemannHypothesis) : RobinStatement
-- ∀ n > 5040, σ(n) < e^γ n log log n
```

proved in `Robin/Main.lean`.

## Route

We do not go through superabundant or colossally abundant numbers explicitly. Instead we use
the bound that defines colossally abundant numbers, for an exponent chosen as a function of
`n`, and only one analytic input from RH: the weighted explicit formula of erdos-985.

Notation: `x > 1` real, `L = log x`, `ε = ε(x) = log(1 + 1/x)/log x`,
`c_p = −log(1 − 1/p)`, `θ, ψ` Chebyshev's functions, `Ψ₁(t) = Σ_{n≤t} Λ(n)(t − n) = ∫₀ᵗ ψ`,
`w(t) = (1 + log t)/(t² log² t) = −(d/dt) 1/(t log t)`.

### 1. Elementary bound (`Robin/Elementary/SigmaBound.lean`, proved)

For `n ≥ 1`, `x ≥ 3`:

```
log(σ(n)/n) ≤ ε log n + Σ_{p≤x} (c_p − ε log p) − Σ_{p≤x} min(1/p², ε log p).
```

`σ(n)/n = ∏_{p^k ∥ n} (1 + p⁻¹ + ⋯ + p⁻ᵏ)`, and each local term
`g_p(k) = log(1 + ⋯ + p⁻ᵏ) − kε log p` is `≤ 0` for `p > x` (since `log(1+1/t)/log t` decreases)
and `≤ c_p − ε log p − min(1/p², ε log p)` for every prime (cases `k = 1`, `k ≥ 2`); that bound
is `≥ 0` for `p ≤ x`.

### 2. Reduction (`Robin/Main.lean`, proved)

If `log n ≤ e^{30}`: cited computation (§5). Otherwise put `x = log n`. By §1,

```
log(σ(n)/n) ≤ ε(x − θ(x)) + Σ_{p≤x} c_p − gain(x),   gain(x) = Σ_{p≤x} min(1/p², ε log p),
```

and §4 shows the right side is `< γ + log log x = γ + log log log n`.

### 3. RH input

* `Robin/RH/Bach.lean`: RH-only version of erdos-985's `bach_principal_of_GRH`:
  `|Σ_{n<x} Λ(n)(1 − n/x) − x/2| ≤ √x/20 + 3` for natural `x ≥ 1`
  (explicit formula over the zeros of `ξ`, with `Σ_ρ 1/|ρ(ρ+1)| ≤ 2 + γ − log 4π < 1/20` on the
  critical line). Hence `|Ψ₁(m) − m²/2| ≤ m^{3/2}/20 + 3m`.
* `Robin/RH/Psi1.lean`: `Ψ₁` is continuous with right derivative `ψ`;
  `|Ψ₁(t) − t²/2| ≤ t^{3/2}/20 + 4t` for real `t ≥ 16` (linear interpolation);
  `|ψ(s) − s| ≤ s^{3/4}` for `s ≥ 1000` (differencing `Ψ₁` with step `s^{3/4}`);
  `θ(t) − t = O(t^{3/4})`.

No zero-counting `N(T)`, no truncated explicit formula and no pointwise Schoenfeld bound are
needed: the only quantities that need precision `1/(√x log x)` are integrals of `ψ` against
smooth weights, which we integrate by parts against `Ψ₁`. (Pointwise `|θ(x) − x|` enters only
multiplied by `1/(x log x) − ε = O(1/(x² log x))`, thanks to the choice of `ε`.)

### 4. Analytic estimate for `x ≥ e^{30}` (`Robin/Main/Estimate.lean`, assembled)

* Mertens with remainder (`Robin/Mertens/Identity.lean`, proved from §4a):
  `Σ_{p≤x} c_p ≤ γ + log log x + (θ(x) − x)/(x log x) − ∫_x^∞ (θ(t) − t) w(t) dt`.
  Abel summation makes `Σ_{p≤x} 1/p − log log x − (θ(x)−x)/(x log x) + ∫_x^∞ (θ − t) w`
  constant, and `Σ_p (c_p − 1/p)` converges.
* 4a. Mertens' constant (`Robin/Mertens/Abelian.lean`): if `Σ_{p≤x} c_p − log log x → C` then
  `C = γ`, via `(s−1)∫₁^∞ (Σ_{p≤t} c_p) t^{−s} dt = Σ_p c_p p^{1−s} = log ζ(s) + o(1)`,
  `(s−1)ζ(s) → 1`, Mathlib's `γ = −log(s−1) − (s−1)∫₁^∞ log log t · t^{−s} dt`, and an Abelian
  argument.
* Boundary term: `ε(x − θ(x)) + (θ(x) − x)/(x log x) = (θ(x) − x)(1/x − log(1+1/x))/L ≤ 1.39/(xL)`.
* Tail (`Robin/Main/Tail.lean`): `∫_x^∞ (t − θ) w ≤ (2.4 + 3.3 x^{−1/8} + 26 x^{−1/4})/(√x L)`:
  `t − ψ` part by parts against `E = Ψ₁ − t²/2` (`≤ 0.314/(√x L)`), and
  `ψ − θ ≤ ψ(√t) + ψ(t^{1/3}) + ψ(t^{1/5})` (Mathlib, Costa Pereira) for the rest
  (`≤ (31/30)·2/(√x L) + …`).
* Gain (`Robin/Main/Gain.lean`): with `Y² log Y = 1/ε` (so `√x ≤ Y ≤ √(2(x+1))`),
  `gain = εθ(Y) + Σ_{Y<p≤x} 1/p² = θ(x)/(x² L) + ∫_Y^x θ(t) v(t) dt`,
  `v = −(d/dt) 1/(t² log t)`, and `∫_Y^x t v ≥ (1/(Y log Y) − 1/(xL))(1 + L/(L+2))`. Result:
  `gain ≥ (2.67 − 60 x^{−1/4})/(√x L)`.
* Numerics: with `r = x^{−1/8} ≤ 1/40`, `1.39 r⁴ + 2.4 + 3.3 r + 26 r² < 2.67 − 60 r²`.

The asymptotic margin is Robin's: gain `2√2 ≈ 2.83` against `2` from the prime squares in
`ψ − θ` and `≈ 0.05·5` from the zeros (our partial integration wastes a factor of about 5 over
the optimal `2 + γ − log 4π ≈ 0.046`); at `x = e^{30}` the constants are
`2.678 > 2.38 + o(1)`.

### 5. The range `5040 < n ≤ exp(e^{30})` (`Robin/Compute/`, `RobinCompute/`, proved)

Previously the hypothesis `RobinVerifiedRange` (Morrill–Platt). Now proved by a verified
computation; `Robin.robin_verified_range : RobinVerifiedRange`.

**Sizing (2026-11-24).** The analytic threshold `x = log n ≥ e^{30} ≈ 1.0686·10^{13}` is set by
the `x^{−1/8}`, `x^{−1/4}` error terms coming from `|ψ(s) − s| ≤ s^{3/4}` (only the integrated
`Ψ₁` bound is available). Re-solving `3.3r + 86r² = 0.27` with the present constants only lowers
it to `x ≈ 1.5·10^{11}` (`e^{25.7}`), and every lemma is written for `log x ≥ 30`; not worth it.
Instead the whole range is computed:

* Envelope: `log(σ(n)/n) ≤ εx + Σ_p max_k(log(σ(p^k)/p^k) − kε log p)` for all `n`, `x = log n`.
  For `ε ≈ log(1+1/B)/log B` only primes `< B` contribute; the line `εx + C` is nearly tangent
  to `γ + log log x` at `x ≈ θ(B)` and stays below it on an interval of width `≈ 1.2 x^{3/4}`
  (prototype in C, CA hull up to `10^8`: normalised margin `(γ + log log x − log(σ(N)/N))·√x log x`
  is `0.13` at `x = 10.9` (`N = 55440`), `0.76–0.9` for `10^3 ≤ x ≤ 10^8`).
* So `≈ 4–8 X^{1/4}` checkpoints suffice (15 746 were used, spacing `2^{⌊(3/4)log₂ B⌋}`), but
  each needs `Σ log(1+1/p)` over all primes `p < B` to absolute precision `≈ 10^{−9}` at the
  top: the primes up to `1.07·10^{13}` (`≈ 3.6·10^{11}`) must be enumerated.
* Cost: segmented sieve in compiled Lean, `1.2·10^8` numbers/s/core unloaded, so `≈ 25`
  core-hours for the sieve; extras at a checkpoint near the top `≈ 4 s` (sieve to
  `Q ≈ 4.2·10^6` plus two logs per prime). `native_decide` on a non-precompiled module runs
  `≈ 75×` slower (interpreter), hence `RobinCompute` is a core-only, precompiled library.
* Pass 1 (untrusted executable, same code) produced the 624 boundary states; it took
  `≈ 109` process-hours wall on a heavily shared machine (load 120–220).

**Checker** (`RobinCompute/Core.lean`): fixed point `D = 2^{96}`; segments `[B, B+h)`,
`h = 2^{min(22, ⌊log₂B⌋−10)}`; exact per-prime logs below `2^{26}`, moments `(count, Σi, Σi²)`
above; chunk `i` is `[i·2^{34}, (i+1)·2^{34})`, `i < 623`; `5040 < n ≤ 10^4` checked directly;
`γ ≥ H_N − log N − 1/(2N)`, `N = 2^{20}`.

**Soundness** (`Robin/Compute/`): `Log.lean` (series bounds, `γ`), `Envelope.lean`,
`Sieve.lean` (a marked number is a proper multiple; scans are finset sums), `Step.lean`,
`Checkpoint.lean` (`Valid` is preserved), `Run.lean`, `Range.lean` (assembly).

## Status

Everything is proved; the computed range of §5 is an explicit hypothesis. There is no `sorry`
in the repository. Output of `#print axioms` (2026-11-24):

```
'Robin.robin_of_RH_of_verified' depends on axioms: [propext, Classical.choice, Quot.sound]
'Robin.lagarias_of_RH_of_verified' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Robin.Lagarias.midCheck_range._native.native_decide.ax_1_1]
'Robin.main_estimate' depends on axioms: [propext, Classical.choice, Quot.sound]
```

| File | Content | Status |
|---|---|---|
| `Robin/Defs.lean` | shared definitions | done |
| `Robin/Elementary/SigmaBound.lean` | §1 | proved |
| `Robin/Main.lean` | §2, `robin_of_RH_of_verified` | proved |
| `Robin/RH/Bach.lean` | §3 explicit formula under RH | proved |
| `Robin/RH/Psi1.lean` | §3 `Ψ₁`, `ψ` bounds | proved |
| `Robin/Mertens/Abelian.lean` (+`Abelian/{Limit,Mellin,Zeta}.lean`) | §4a Mertens' constant `= γ` | proved |
| `Robin/Mertens/Identity.lean` (+`Identity/Abel.lean`) | Mertens with remainder | proved |
| `Robin/Main/Tail.lean` | tail integral | proved |
| `Robin/Main/Gain.lean` (+`Gain/{Basic,Y,Abel,Integrals,Errors,Core}.lean`) | gain lower bound | proved |
| `Robin/Main/Estimate.lean` | §4 assembly and numerics | proved |
| `Robin/Small.lean` | §5 | `RobinVerifiedRange` (a `Prop`, used as a hypothesis) |

### Stretch goal: `Robin.lagarias_of_RH_of_verified : RiemannHypothesis → RobinVerifiedRange → LagariasStatement` (proved)

`Robin/Lagarias.lean` (+`Lagarias/{Bounds,Finite}.lean`):
* `n > 5040`: Robin plus `H_n ≥ log n + γ`, so `exp H_n ≥ e^γ n` and `log H_n ≥ log log n`.
* `1 ≤ n ≤ 12`: exact rational `H_n` with certified rational exp/log bounds, `decide +kernel`.
* `13 ≤ n ≤ 5040`: `σ(n) ≤ t + 0.57688 + exp(0.57688)·n·L` with certified `t ≤ log n`,
  `L ≤ log(t + 0.57688)`, checked over ℚ by **`native_decide`** (`midCheck_range`, documented
  finite check).
