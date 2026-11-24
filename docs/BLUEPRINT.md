# Blueprint: RH ⇒ Nicolas' inequality

Notation: `x` real, `L = log x`, `q = p_k` the `k`-th prime, `N_k = p_1 ⋯ p_k`,
`c_p = −log(1 − 1/p)`, `S(x) = Σ_{p≤x} c_p` (`Robin.primeSum Robin.cp x`), `θ`, `ψ` Chebyshev's
functions, `w(t) = (1 + log t)/(t² log² t)` (`Robin.wM`), `Ψ₁(t) = Σ_{n≤t} Λ(n)(t − n)`.

## Assembly (`Nicolas/Main.lean`)

```lean
theorem Nicolas.nicolas_of_RH (hRH : RiemannHypothesis) : NicolasStatement
```

For `k = j + 1` put `q = nth Prime j`. Rewrite `kthPrimorial (j+1) = q#`
(`kthPrimorial_succ_eq`), `log q# = θ(q)` (`log_primorial`) and
`q#/φ(q#) = exp(S(q))` (`primorial_div_totient`). The goal becomes
`e^γ · log θ(q) < exp S(q)`.

| Range | Lemma | Input |
|---|---|---|
| `q = 2` | inline | `log log 2 < 0` |
| `3 ≤ q ≤ 10^5` | `Nicolas.Check.finite_range` | `native_decide` (step 6) |
| `q ≥ 100001` | `Nicolas.sum_cp_gt_large` + `exp_gamma_mul_log_lt` | RH via `Robin.psi1NatBound_of_RH` |

## Step 1: primorials (`Nicolas/Primorial.lean`)

```lean
theorem kthPrimorial_succ_eq (k : ℕ) : kthPrimorial (k + 1) = primorial (Nat.nth Nat.Prime k)
theorem primorial_div_totient (n : ℕ) :
    (primorial n : ℝ) / (Nat.totient (primorial n) : ℝ) = Real.exp (primeSum cp n)
theorem log_primorial (n : ℕ) : Real.log (primorial n) = θ n
```

`primesLE (nth k) = image nth (range (k+1))`; Euler's product `φ(n)·∏p = n·∏(p − 1)`.

## Step 2: Mertens as an identity (`Nicolas/Mertens.lean`)

```lean
theorem mertens_eq (hθ : ∃ C, ∀ t : ℝ, 2 ≤ t → |θ t - t| ≤ C * t ^ ((3 : ℝ) / 4))
    {x : ℝ} (hx : 2 ≤ x) :
    IntegrableOn (fun t => (θ t - t) * wM t) (Ioi x) ∧
    primeSum cp x = γ + log (log x) + (θ x - x) / (x * log x)
      - (∫ t in Ioi x, (θ t - t) * wM t) - tailK x
theorem tailK_le_div {x : ℝ} (hx : 0 < x) : tailK x ≤ 4 / x
theorem loglog_theta_le {x : ℝ} (hx : 3 ≤ x) :
    log (log (θ x)) ≤ log (log x) + (θ x - x) / (x * log x)
```

`tailK x = Σ_{p>x}(c_p − 1/p) ≤ Σ_{n>⌊x⌋} 2/n² ≤ 4/(⌊x⌋+1)` (Mathlib's `sum_Ioo_inv_sq_le`).
The proof of `mertens_eq` is robin-rh's `mertens_RH` without dropping `tailK`: robin-rh's
`D1_eq` (Abel summation) and `mertens_const_eq_gamma` (the constant is `γ`). The hypothesis is
robin-rh's `theta_sub_bound` (RH).

`loglog_theta_le`: `log(a/b) ≤ a/b − 1` twice, with `θ(3) = log 6 > 1`.

Subtracting, for `x ≥ 3`:
`S(x) − γ − log log θ(x) ≥ J(x) − tailK(x)`, where `J(x) = −∫_x^∞ (θ − t) w`. The two
`(θ(x) − x)/(x log x)` terms cancel; this is where the sign of the secondary term enters.

## Step 3: the `t − ψ` part of `J` (`Nicolas/Tail.lean`)

```lean
lemma integral_sub_psi_wM_ge (hB : Psi1NatBound) {x y : ℝ} (hx16 : 16 ≤ x)
    (hL : 11 ≤ log x) (hxy : x ≤ y) :
    -(2 * ((12 / 11) * Abd x / log x)
        + (2.29 / log x) * (x ^ (-(1 : ℝ) / 2) / 10 + 4 * x ^ (-(1 : ℝ))))
      ≤ ∫ t in x..y, (t - ψ t) * wM t
```

By parts against `E = Ψ₁ − t²/2` (robin-rh's `integral_sub_psi_wM`), with
`|E(t)| ≤ t^{3/2}/20 + 4t` (robin-rh's `E1_le_Abd`, from erdos-985's explicit formula under RH),
`w(t) ≤ (12/11)/(L t²)` and `|w'(t)| ≤ 2.29/(L t³)` for `log t ≥ L ≥ 11`. Then `y → ∞`.

## Step 4: the `ψ − θ` part of `J` (`Nicolas/Tail.lean`, unconditional)

```lean
lemma psi_ge_068 {s : ℝ} (hs : 100 ≤ s) : 0.68 * s ≤ ψ s
lemma integral_GN {x : ℝ} (hx : 1 < x) :
    IntegrableOn GN (Ioi x) ∧ ∫ t in Ioi x, GN t = 2 * x ^ (-(1 : ℝ) / 2) / log x
lemma psi_sub_theta_wM_ge {x t : ℝ} (hx : 10000 ≤ x) (hL : 11 ≤ log x) (ht : x ≤ t) :
    0.68 * (12 / 13) * GN t ≤ (ψ t - θ t) * wM t
```

`ψ(t) − θ(t) ≥ ψ(√t)` (Mathlib's Costa Pereira bound `psi_sub_theta_ge_psi_add_psi_add_psi`),
`ψ(s) ≥ ⌊s⌋ log 2 ≥ 0.68 s` for `s ≥ 100` (`psi_ge_of_seven_le`). With
`g(t) = 2/(√t log t)`, `GN = −g' = t^{−3/2}(log t + 2)/log² t` and
`√t·w(t) = t^{−3/2}(log t + 1)/log² t ≥ (12/13)·GN(t)` for `log t ≥ 11`. Hence
`∫_x^∞ (ψ − θ) w ≥ 0.68 · (12/13) · 2/(√x log x)`.

## Step 5: the analytic range (`Nicolas/Tail.lean`, `Nicolas/Analytic.lean`)

```lean
theorem tail_lower (hB : Psi1NatBound) {x : ℝ} (hx : 100000 ≤ x) (hL : 11 ≤ log x) :
    IntegrableOn (fun t => (θ t - t) * wM t) (Ioi x) ∧
    0.86 / (√x * log x) ≤ -∫ t in Ioi x, (θ t - t) * wM t
theorem sum_cp_gt_large (hB : Psi1NatBound) {x : ℝ} (hx : 100000 ≤ x) :
    γ + log (log (θ x)) < primeSum cp x
```

With `s = x^{−1/2} ≤ 1/316`: `J·L/s ≥ 1.2554 − 0.1091 − 0.229 − 17.9 s ≥ 0.86`. Then
`tailK ≤ 4/x < 0.86/(√x L)` because `4L ≤ 20 x^{1/5} < 0.86 x^{1/2}` (`log x ≤ 5x^{1/5}`,
`x^{3/10} ≥ 31` for `x ≥ 10^5`). `log(10^5) ≥ 11` from `e < 2.7182818286`.

The threshold `10^5` is where the finite range below is cheap and the slack in the check is
still three times the error of the `γ` bound; the analytic argument itself would work from
about `x = 10^4` with these constants (`J ≈ 0.7/(√x L)` against `T ≤ 4/x`).

## Step 6: the finite range (`Nicolas/Check/`)

```lean
theorem Nicolas.Check.loop_ok : (loop bound 1 init).ok = true       -- native_decide
theorem Nicolas.Check.finite_range {p : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p) (hpB : p ≤ 100000) :
    Real.exp γ * Real.log (θ (p : ℝ)) < Real.exp (primeSum cp (p : ℝ))
```

The checker (`Defs.lean`) walks `n = 1, …, 10^5` with state `(R, T, ok)` in `ℚ`:

* at a prime `n` (test `2 ≤ n ∧ minFac n = n`): `R ← rdDown(R · n/(n − 1))`,
  `T ← T + logUp n`, and for `n ≥ 3`, `ok ← ok ∧ EU · logUp T < R`;
* `rdDown`/`rdUp` round to multiples of `2^{−64}`;
* `logUp q = rdUp(e · 0.6931471808 + logUpR(q/2^e))` with `e = ⌊log₂⌊q⌋⌋`, and
  `logUpR r = Σ_{i<40} y^{i+1}/(i+1) + y^{41}/(1 − y)`, `y = 1 − 1/r ∈ [0, 1/2]`;
* `EU = expUpper(0.5774)` (robin-rh's certified Taylor bound), `e^γ ≤ EU` from erdos-985's
  `γ < 0.5774`.

Soundness (`Sound.lean`): `log_le_logUpR` (Mathlib's `abs_log_sub_add_sum_range_le`),
`log_le_logUp`, `exp_gamma_le_EU`, and the invariant `Inv m st`:
`R ≤ exp S(m)`, `θ(m) ≤ T`, `ok → ∀ prime 3 ≤ p ≤ m, e^γ log θ(p) < exp S(p)`, preserved by
`step` (`inv_step`). `loop_run` identifies the tail-recursive `loop` that is executed with the
structural `run` that is reasoned about.

Sizing (float computation, `scratchpad`): the slack `S(p) − γ − log log θ(p)` is about
`2/(√p log p)` throughout; its minimum on `10^4 ≤ p < 10^5` is `5.78·10^{−4}` (at
`p = 99991`), on `10^5 ≤ p < 10^6` it is `1.49·10^{−4}`. The `γ` bound costs
`0.5774 − γ = 1.84·10^{−4}`, so the finite range cannot go past about `7·10^5` without a sharper
upper bound for `γ`. Replacing `EU` by `1.0004·EU` makes the check fail (first at `p = 98057`).
