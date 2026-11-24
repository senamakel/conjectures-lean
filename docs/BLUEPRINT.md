# Blueprint

Source: Lamzouri, Li, Soundararajan, *Conditional bounds for the least quadratic non-residue
and related problems*, Math. Comp. 84 (2015), arXiv:1309.3595 (corrected v3 source,
`QuaResL1Corrected.tex`). Every step below is a Lean statement with its constant. All of them
are proved. Notation: `χ` is primitive and non-trivial mod `N`; `Λ(s, χ)` is Mathlib's
`completedLFunction` (no conductor factor); `D(s) = Λ'/Λ(s)`; `Z2 = Σ_ρ m_ρ/|ρ|²`
(`= 2|Re B(χ)|` in LLS).

## Assembly (top down)

1. `LLS.leastNonresidueBelowLogSq_of_GRH : GRH → LeastNonresidueBelowLogSq` (LLS Cor. 1.2):
   `q < 2^12` by kernel-checked certificates (`LLS/NonresidueCert.lean`), `q ≥ 2^12` by
   `LLS.nonresidue_large`.
2. `LLS.bach_of_GRH : GRH → Ankeny.BachSubgroupBound (11/4)`: `q < 2^18` by
   `LLS.bach_small114` (ankeny-grh's checker, 16 `native_decide` chunks), `q ≥ 2^18` by
   `LLS.bach_large114`. Corollaries: `LeastNonresidueBound (11/4)`, `Miller.MillerStatement (11/4)`.
3. `LLS.bach_of_goodQ`: `GoodQ c q` (some `64 ≤ x ≤ c log² q` with `Φ(x, log q) > 0`,
   `β ≤ κ`) gives the subgroup bound at `q`. Same for primes with `GoodP`/`Φ₁`.
4. `GoodQ (11/4) q` for `2^18 ≤ q < 2^700`: 28 certified intervals
   (`Numerics/Intervals114.lean`); `q ≥ 2^700`: `LLS.goodQ_tail114`. `GoodP 1 q` for `2^12 ≤ q < 2^700`: 153 intervals
   (`Numerics/IntervalsP.lean`); `q ≥ 2^700`: `LLS.goodP_tail`.
5. `LLS.Phi_nonpos`: if `χ ≠ 1` mod `q` is `1` on every `n ≤ x` prime to `q`, `x ≥ 64` and
   `β(x) ≤ κ(x)`, then `Φ(x, log q) ≤ 0`, where with `s = √x`, `l = log x`,
   `K = (s + 1 + l/2)/(1 + 1/x − 2/s)`, `κ = K(1 − 1/x) + l/2`, `β = l²/(2 log 17) + K/8`:
   `Φ = x − (3/20)s − 3l − 3 + 2K(l − 2) − κL − 2K E(x) + ½ log π · l − Ẽ(x) − βL
        − Σ_{p<17} max(0, W_p − β log p)`.
   `LLS.Phi1_nonpos` is the version for prime `q > x`, with no loss terms (`Φ₁`).
6. `LLS.key` (LLS §3): with `ψ` the primitive character inducing `χ`, conductor `f`,
   `l_f = log f`, `R = {p ∣ q : p ∤ f}`:
   * `Z (1 + 1/x − 2/√x) ≤ l_f (1 − 1/x) − 2(log x − 2 − Lc_q − Lc_R) + 2E(x)`,
   * `x − (3/20)√x − 3 log x − 3 − Ll_q − Ll_R ≤ (√x + 1)Z + ((l_f + Z)/2) log x
       − ½ log π log x + Ẽ(x)`,
   * `l_f + Σ_{p∈R} log p ≤ log q`.
   Obtained by symmetrising over `ψ` and `ψ⁻¹` (`Z2 ψ = Z2 ψ⁻¹ = log f + Re D(1,ψ) + Re D(1,ψ⁻¹)`).
7. Losses (`LLS/Losses.lean`, `Numerics/Budget.lean`): `Σ_{n≤x} Λ(n)w(n) Re φ(n) ≥ Σ Λ w −
   Σ_{p∣q} Σ_{p^k≤x} Λ w − Σ_{p∈R} Σ_{p^k≤x} Λ w`;
   `Σ_{p^k≤x} log p log(x/p^k) ≤ (log x − ½ log p)²/2`, `Σ_{p^k≤x} Λ/p^k (1 − p^k/x) ≤
   log p/(p − 1)` (LLS Lemma 3.1, sharpened).

## Analytic inputs (each proved, standard axioms only)

| Lean | LLS | Statement |
|---|---|---|
| `LLS.re_logSum_le` | Lemma 2.2 | `Re Σ_{n≤x} Λχ(n) log(x/n) ≤ (√x+1) Z2 + (log N + Re D(1,χ⁻¹)) log x − ½ log π log x + π²/6 − (γ/2) log x` |
| `LLS.re_cesShift_le` | Lemma 2.3 | `Re Σ_{n<x} Λχ(n)/n (1−n/x) ≤ −Re D(1,χ) − (log N + Re D(1,χ⁻¹))/x + Z2/√x + E(x)`, `E(x) = −½(1−1/x) log π − (γ/2)(1−1/x) + (log x+2)/x` |
| `LLS.Z2_eq` | (2.4) | `Z2 = log N + Re D(1,χ) + Re D(1,χ⁻¹)` |
| `LLS.psiLog_ge` | Lemma 2.1 (weaker) | `Σ_{n≤x} Λ(n) log(x/n) ≥ x − (3/20)√x − 3 log x − 3` (Abel summation from erdos-985's principal bound) |
| `LLS.vonMangoldt_ces_ge` | Lemma 2.4 (weaker, unconditional) | `Σ_{n<x} Λ(n)/n (1−n/x) ≥ log x − 2` |

`re_logSum_le` needs a new Perron kernel `x^s/s²` (`Analytic/Log/Perron.lean`: Mellin
transforms of `log t` and `log² t` on `(0,1]`, the weighted Perron formula, the residues of
`x^s/((s−w)s²)` and `x^s/s³`), an exact identity
`S = −Σ_ρ m_ρ (x^ρ − 1)/ρ² − D(0) log x + Γ̃(x)` (`Log/Identity.lean`) and the gamma part via the
digamma series (`Log/Gamma.lean`). `re_cesShift_le` reuses erdos-985's Cesàro kernel with the
coefficients `χ(n)Λ(n)/n` and zeros shifted to `ρ − 1` (`Analytic/Shift/`).

## Numerics

Each certified interval `[Q_a, Q_b)` fixes `x ≤ c (log Q_a)²`; bounds
`2^k ≤ m^64 ≤ 2^{k'}` for `log Q_a`, `log Q_b`, `log x` (`decide +kernel`), rational bounds for
`√x`, and a rational inequality `PhiLo > 0` (`norm_num`). `LLS.Phi_ge_PhiLo` proves
`PhiLo ≤ Φ` by monotonicity. Interval data comes from `scripts/emitfile.py` (`c = 11/4`) and
`scripts/emit1.py` (`c = 1`, primes).

Sizing (Python, worst case over the small prime factors of `q`, exact prime-power losses): the
analytic argument with these constants needs `q ≥ 2^12.3` for `c = 3`, `2^16.9` for `c = 5/2`,
`2^21.1` for `c = 9/4` and `2^28.7` for `c = 2`. With the cruder bounds actually formalised
(`llp ≤ (l − ½ log p)²/2`, `β = l²/(2 log 17) + K/8`), `c = 11/4` fails just above `2^17` but
holds from `2^18` (so the finite check runs to `2^18`); `c = 5/2` would need `2^20`. Prime moduli work with `c = 1` from
`q ≈ 2600`; the certificates start at `2^12`.
