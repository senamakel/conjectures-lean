# Blueprint: Axer's bound `E(x) ≪ x^{2/5+ε}` under RH

Notation: `μ` is the Möbius function, `M(k) = ∑_{d ≤ k} μ(d)` (`Erdos969.Mr`), `N` a natural
number, `Q(N) = #{n ≤ N squarefree}`, `E(N) = Q(N) − (6/π²) N`. Hypothesis `MBound K α`:
`|M(k)| ≤ K (k+1)^α` for every `k ≥ 0`, with `0 ≤ α < 2`.

## 1. The identity (`Erdos969/Identity.lean`)

`∑_{d² ∣ n} μ(d) = 1` if `n` is squarefree, else `0`. Write `n = b² a` with `a` squarefree
(`Nat.sq_mul_squarefree_of_pos`). Then `d² ∣ n ⇔ d ∣ b` (`sq_dvd_iff`: take `g = gcd(d, b)`,
`d = g d'`, `b = g b'`; `d'² ∣ b'² a` and `gcd(d', b') = 1` give `d'² ∣ a`, so `d' = 1`), and
`∑_{d ∣ b} μ(d) = [b = 1]` from `μ * ζ = 1`. Summing over `n ≤ N` and swapping:
`Q(N) = ∑_{d ≤ N} μ(d) ⌊N/d²⌋` (`squarefreeCounting_eq`).

## 2. The tail of `∑ μ(d)/d²` (`Erdos969/Series.lean`)

* `hasSum_moebius_sq`: `∑ μ(n)/n² = 6/π²`, from `L(ζ,2) L(μ,2) = 1` and `ζ(2) = π²/6` (Mathlib).
* `abs_tail_le`: for `Y ≥ 1`, `|6/π² − ∑_{d ≤ Y} μ(d)/d²| ≤ C₁ Y^{α−2}` with
  `C₁ = 2K 2^α (1 + 3/(2−α))`. Abel summation of the block `d > Y` against `w(d) = d^{-2}`
  (`Mertens.abel_identity`): partial sums `|M(Y+n+1) − M(Y)| ≤ 2K 2^α u^α`, `u = Y+n+1`;
  `|w(n+1) − w(n)| ≤ 3 u^{-3}`; `∑_n u^{α−3} ≤ Y^{α−2}/(2−α)` by comparison with an integral
  (`sum_rpow_neg_le_of_gt`). The finite bound is uniform in the length, so it passes to the limit.

## 3. The hyperbola split (`Erdos969/Hyperbola.lean`)

`T = ∑_{Y < d ≤ N} μ(d) ⌊N/d²⌋`. Since `⌊N/d²⌋ = #{m ≥ 1 : m d² ≤ N}` and
`m d² ≤ N ⇔ d ≤ ⌊√⌊N/m⌋⌋ =: s(m)`, `T = ∑_{m ≤ N} (M(s(m)) − M(Y))⁺` (the bracket is the sum of `μ`
over `Y < d ≤ s(m)`, zero when `s(m) ≤ Y`; `T_eq`). It vanishes for `m > X = ⌊N/Y²⌋`
(`inner_eq_zero`). For `m ≤ X`: `|·| ≤ K (s(m)+1)^α + K (Y+1)^α`, and
`(s(m)+1)^α ≤ 2^α (N/m)^{α/2}` (`sqrt_succ_rpow_le`). With `β = α/2` and
`∑_{m ≤ X} m^{-β} ≤ X^{1−β}/(1−β)` (`sum_rpow_neg_le`, by Bernoulli),
`|T| ≤ C₂ N Y^{α−2}`, `C₂ = K 2^α (1/(1−α/2) + 1)` (`abs_T_le`).

## 4. Assembly (`Erdos969/Main.lean`)

`E(N) = −R + N (P_Y − 6/π²) + T`, where `P_Y = ∑_{d ≤ Y} μ(d)/d²` and
`R = ∑_{d ≤ Y} μ(d) {N/d²}`, `|R| ≤ Y`. So `|E(N)| ≤ Y + (C₁ + C₂) N Y^{α−2}`
(`abs_error_le`). Take `Y = ⌈N^θ⌉`, `θ = 1/(3−α)`: then `N Y^{α−2} ≤ N · N^{θ(α−2)} = N^θ`
(`squarefreeError_le`: `|E(N)| ≤ C N^{1/(3−α)}`).

Under RH, `Mertens.abs_mertens_nat_le` gives `MBound K (1/2 + 3ε')` for `ε' ≤ 1/12`, and
`1/(3 − α) = 2/(5 − 6ε') ≤ 2/5 + ε'`. Hence `AxerBound` (`axer_of_RH`). With `ε = 1/20` this is
`E = O(x^{9/20}) = o(√x)` (`erdos_969_prime_number_theorem_of_RH`).

## What is not here

The exponent `1/(3−α)` is the limit of this method: with `α = 1/2` it is exactly `2/5`.
Section 6 reaches `1/3` by a contour argument. The exponents `9/28`, `8/25`, `7/22`, `17/54` and
`11/35` need the truncated Fourier expansion of the sawtooth function and van der Corput
exponent pairs, which Mathlib does not have.

## 5. `k`-free numbers (`Erdos969/KFree/`)

The same argument with `d²` replaced by `d^k`, `k ≥ 2`, `0 ≤ α < k`:

* Identity (`KFree/Identity.lean`): `{d : d^k ∣ n} = divisors (Nat.floorRoot k n)`
  (`Nat.pow_dvd_iff_dvd_floorRoot`), and `n` is `k`-free iff `Nat.floorRoot k n = 1`, so
  `∑_{d^k ∣ n} μ(d) = [n k-free]` and `Q_k(N) = ∑_{d ≤ N} μ(d)⌊N/d^k⌋` (`kFreeCounting_eq`).
  `kFreeCounting_two`, `kFreeCountingError_two` (`ζ(2) = π²/6`) tie `k = 2` to `Statement.lean`.
* Series (`KFree/Series.lean`): `∑ μ(n)/n^k = 1/(riemannZeta k).re` from
  `LSeries_zeta_mul_Lseries_moebius` (the `L`-value is real because the terms are). Weights:
  `(u+1)^k − u^k ≤ k(u+1)^{k−1}` (geometric sum), so `|1/(u+1)^k − 1/u^k| ≤ k/u^{k+1}`. Abel
  summation gives the tail `≤ 2K 2^α (1 + k/(k−α)) Y^{α−k}` (`abs_tail_le_pow`).
* Hyperbola (`KFree/Hyperbola.lean`): `iroot k n = Nat.findGreatest (· ^ k ≤ n) n`, with
  `d ≤ iroot k n ↔ d^k ≤ n`. `T = ∑_{m ≤ N/Y^k} ∑_{Y < d ≤ iroot k ⌊N/m⌋} μ(d)`,
  `(iroot k ⌊N/m⌋ + 1)^α ≤ 2^α (N/m)^{α/k}`, `β = α/k < 1`, and
  `N^β (N/Y^k)^{1−β} = N Y^{α−k}`: `|T| ≤ K 2^α (1/(1−α/k) + 1) N Y^{α−k}` (`abs_T_le_pow`).
* Assembly (`KFree/Main.lean`): `|E_k(N)| ≤ Y + C N Y^{α−k}`, `Y = ⌈N^θ⌉`, `θ = 1/(k+1−α)`
  (`kFreeError_le`). Under RH, `α = 1/2 + ε₁`, `ε₁ = min(ε, 1/12)`, from
  `Mertens.abs_mertens_nat_le` at `ε₁/3`; with `t = 2/(2k+1)`,
  `(t + ε₁)(k + 1/2 − ε₁) = 1 + ε₁(k + 1/2 − t − ε₁) ≥ 1`, so `θ ≤ t + ε` (`axerKFree_of_RH`).

## 6. Montgomery–Vaughan's `1/(k+1)` (`Erdos969/MV/`)

Why the hyperbola method stops at `2/(2k+1)`: at `Y = x^{1/(k+1)}` the `d > Y` part,
`∑_{m ≤ X} (M((x/m)^{1/k}) − M(Y))` with `X = Y`, has `X` terms of size up to `Y^{1/2}` at the
bottom of the range, and pointwise bounds give `x^{3/(2(k+1))}`. Montgomery–Vaughan's Theorem 1
(as summarised by Powell 2009) handles the `d > Y` part through the Dirichlet series
`ζ(s) ∑_{d>Y} μ(d) d^{−ks}`, so the cancellation among the `m` comes from moving the line of
integration to `σ = 1/2 + ε`.

* `MV/Perron.lean`, `norm_sum_Icc_le`. For `a : ℕ → ℂ` with `∑ ‖a n‖/n³ < ∞` and `Φ` holomorphic
  on `σ₀ ≤ σ ≤ 3`, `Φ = L(a, ·)` on `σ = 3`, bounded there, `O((|t|+2)^{3/2})` on the strip for
  `|t| ≥ 1`, and `‖Φ(σ₀+it)‖ ≤ A(|t|+2)^ε`: `‖∑_{n≤N} a n‖ ≤ K A (N+1)^{σ₀+2ε}`, `K = K(σ₀, ε)`.
  Proof: `ces a N = ∑_{0<n<N} a n (N − n) = (1/2π)∫ N Φ(s) N^s/(s(s+1)) dt` (erdos-985's
  `perron_weighted` on `σ = 3`, then `Mertens.integral_vertical_eq_of_strip`);
  `∑_{n≤N} a n = ces a (N+1) − ces a N`; `‖(N+1)^{s+1} − N^{s+1}‖ ≤ 2(N+1)^{σ+θ}‖s+1‖^{1−θ}`
  (interpolating the trivial and mean-value bounds), `θ = 2ε`, integrand `≪ (1+|t|)^{−1−ε}`.
* `MV/Twisted.lean`. `twisted_mertens`: `Φ(s) = 1/ζ(s + it)`, `a n = μ(n)n^{−it}`, with
  `‖1/ζ(w)‖ ≤ C(|Im w|+2)^ε` on `Re w ≥ 1/2 + ε` and `(|τ+t|+2)^ε ≤ (|t|+2)^ε(|τ|+2)^ε`, gives
  `‖∑_{n≤N} μ(n)n^{−it}‖ ≤ K(|t|+2)^ε(N+1)^{1/2+3ε}`. `tail_le`: Abel summation of
  `μ(d)d^{−it} · d^{−σ}` over `Y < d ≤ U` (weights `|(u+1)^{−σ} − u^{−σ}| ≤ σu^{−σ−1}`), then
  `U → ∞` (`L(μ, w) = 1/ζ(w)` for `σ > 1`): `‖G_Y(σ+it)‖ ≤ K(1 + σ/(σ−β))(|t|+2)^ε Y^{β−σ}`,
  `β = 1/2 + 3ε`. `norm_zeta_le_line`: `‖ζ(σ₀+it)‖ ≤ C(|t|+2)^ε` on `σ₀ ∈ (1/2, 1)`, from
  lindelof-rh's `exists_log_zetaQ`, `norm_log_zetaQ_le`, `norm_le_log_rpow_of_strip`,
  `norm_riemannZeta_le_exp` for `|t| ≥ 1` and compactness for `|t| ≤ 1`.
* `MV/Coeff.lean`. `h(n) = μ(d)` if `n = d^k`, `d > Y` (via `iroot`), `b = h * ζ`.
  `sum_Icc_b`: `∑_{n≤N} b n = ∑_{Y<d≤N} μ(d)⌊N/d^k⌋` (Mathlib's `sum_Ioc_mul_zeta_eq_sum`, then
  `sum_bij_ne_zero` with `n ↦ iroot k n`). `LSeries_b`: `L(b, s) = ζ(s) G_Y(ks)` on `σ > 1`
  (`LSeries_mul'`; `L(h, s)` by `Function.Injective.tsum_eq` along `d ↦ d^k` and
  `natCast_cpow_natCast_mul`). `norm_b_le`: `‖b n‖ ≤ #divisors(n) ≤ n`.
* `MV/Main.lean`. `a n = b n − g`, `g = G_Y(k)` (real: `1/ζ(k) − ∑_{d≤Y} μ(d)/d^k`).
  `Φ(s) = ζ₁(s) · dslope (G_Y(k·)) 1 s` is holomorphic on `{Re(ks) > 1/2}` (`differentiableOn_dslope`)
  and equals `ζ(s)(G_Y(ks) − g)` for `s ≠ 1`, which is `L(a, s)` on `σ = 3` (`LSeries_sub`,
  `LSeries_smul`). On `σ₀ = 1/2 + ε`: `‖Φ‖ ≤ A₀ Y^{β−kσ₀}(|t|+2)^{2ε}`. So
  `|B(N)| ≤ K A₀ Y^{β−kσ₀}(N+1)^{1/2+5ε}` and `|E_k(N)| ≤ Y + C Y^{β−kσ₀}(N+1)^{1/2+5ε}`
  (`abs_error_le_mv`). With `θ = 1/(k+1)`, `Y = ⌈N^θ⌉`, `e = β − kσ₀ < 0`:
  `θe + 1/2 = θ + θ(3−k)ε` and `θ(3−k) ≤ 1`, so both terms are `≤ 2(1 + C) N^{θ+6ε}`, and
  `ε = min(ε'/6, 1/12)` gives `MontgomeryVaughanBound k` (`montgomeryVaughan_of_RH`).

Numerical sanity check (Python, before the Lean proof): with `Y = ⌈N^{1/(k+1)}⌉`,
`|B(N)|/N^{1/(k+1)}` was `0.004, 0.043, 0.042` at `N = 10^6, 10^8, 10^10` for `k = 2` and
`0.011, 0.058, 0.001` at `N = 10^9, 10^12, 10^15` for `k = 3`, against a pointwise-method loss of
`N^{1/(2(k+1))}` (`10` to `75` there).
