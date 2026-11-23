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

### 5. The range `5040 < n ≤ exp(e^{30})` (`Robin/Small.lean`, cited `sorry`)

Morrill–Platt, *Robin's inequality for 20-free integers*, Integers 21 (2021), arXiv:1809.10813,
Theorem 13: Robin's inequality holds unconditionally for `5040 < n ≤ 10^{10^{13.11485}}`
(extending Briggs, Experiment. Math. 15 (2006), who checked all colossally abundant numbers up
to `10^{10^{10}}`). Since `e^{30} < 1.07·10^{13}`, `log n ≤ e^{30}` gives
`n ≤ 10^{4.64·10^{12}}`. This is a finite but enormous computation and is not replayed.

## Status

Everything is proved except the cited computation of §5.

```
#print axioms Robin.robin_of_RH
'Robin.robin_of_RH' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
#print axioms Robin.main_estimate
'Robin.main_estimate' depends on axioms: [propext, Classical.choice, Quot.sound]
```

The single `sorryAx` is `Robin.robin_small_range` (§5). No `native_decide`, no new axioms.

| File | Content | Status |
|---|---|---|
| `Robin/Defs.lean` | shared definitions | done |
| `Robin/Elementary/SigmaBound.lean` | §1 | proved |
| `Robin/Main.lean` | §2, `robin_of_RH` | proved |
| `Robin/RH/Bach.lean` | §3 explicit formula under RH | proved |
| `Robin/RH/Psi1.lean` | §3 `Ψ₁`, `ψ` bounds | proved |
| `Robin/Mertens/Abelian.lean` (+`Abelian/{Limit,Mellin,Zeta}.lean`) | §4a Mertens' constant `= γ` | proved |
| `Robin/Mertens/Identity.lean` (+`Identity/Abel.lean`) | Mertens with remainder | proved |
| `Robin/Main/Tail.lean` | tail integral | proved |
| `Robin/Main/Gain.lean` (+`Gain/{Basic,Y,Abel,Integrals,Errors,Core}.lean`) | gain lower bound | proved |
| `Robin/Main/Estimate.lean` | §4 assembly and numerics | proved |
| `Robin/Small.lean` | §5 | cited `sorry` (by design) |

The remaining `sorry`, verbatim:

```lean
/-- **Cited (Morrill–Platt 2021, arXiv:1809.10813, Theorem 13).** Robin's inequality for `5040 < n ≤ exp(e^{30})`. -/
theorem robin_small_range (n : ℕ) (h1 : 5040 < n) (h2 : Real.log n ≤ Real.exp 30) :
    (σ 1 n : ℝ) < Real.exp Real.eulerMascheroniConstant * n * Real.log (Real.log n)
```

### Stretch goal: `Robin.lagarias_of_RH : RiemannHypothesis → LagariasStatement` (proved)

`Robin/Lagarias.lean` (+`Lagarias/{Bounds,Finite}.lean`):
* `n > 5040`: Robin plus `H_n ≥ log n + γ`, so `exp H_n ≥ e^γ n` and `log H_n ≥ log log n`.
* `1 ≤ n ≤ 12`: exact rational `H_n` with certified rational exp/log bounds, `decide +kernel`.
* `13 ≤ n ≤ 5040`: `σ(n) ≤ t + 0.57688 + exp(0.57688)·n·L` with certified `t ≤ log n`,
  `L ≤ log(t + 0.57688)`, checked over ℚ by **`native_decide`** (`midCheck_range`, documented
  finite check).

```
#print axioms Robin.lagarias_of_RH
[propext, sorryAx, Classical.choice, Quot.sound,
 Robin.Lagarias.midCheck_range._native.native_decide.ax_1_1]
```
