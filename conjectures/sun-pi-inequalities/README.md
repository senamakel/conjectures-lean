# Sun's monotonicity conjectures for `π(kn)^{1/k}` and `π(n²)^{1/n}`, in Lean

Zhi-Wei Sun conjectured on 2014-02-17 that, for every integer `n > 4` and `k = 1, …, n`,
`π(kn)^{1/k} > π((k+1)n)^{1/(k+1)}` (Conjecture 2.7(i) of *Problems on combinatorial properties
of primes*, arXiv:1402.6641, published in the Proc. 7th China–Japan Seminar, World Sci., 2015,
pp. 169–187; also OEIS A238165, conjecture (ii)). On the same day he conjectured that
`π(n²)^{1/n}` is strictly decreasing for `n ≥ 3` (Conjecture 2.14(ii) there; OEIS A038107,
conjecture (i), "to the limit 1"). This package proves both statements in Lean, with no
hypothesis. The arguments are elementary: Chebyshev's lower bound `ψ(x) ≥ x log 2`, a count of
the integers prime to 6 or to 210 in a short interval, and a finite computation. Nothing here
uses RH. We found no proof of either statement in the sources listed below (searched
2026-11-26).

## Headline theorems

```lean
theorem SunPi.sun_2_7_i : SunConjecture_2_7_i
theorem SunPi.oeis_A238165_ii : OeisA238165_ii
theorem SunPi.sun_2_14_ii : SunConjecture_2_14_ii
theorem SunPi.oeis_A038107_i : OeisA038107_i

-- the integer forms they come from
theorem SunPi.sun_2_7_i_nat (n k : ℕ) (hn : 4 < n) (hk1 : 1 ≤ k) (hkn : k ≤ n) :
    π ((k + 1) * n) ^ k < π (k * n) ^ (k + 1)
theorem SunPi.sun_2_14_ii_nat (n : ℕ) (hn : 3 ≤ n) :
    π ((n + 1) ^ 2) ^ n < π (n ^ 2) ^ (n + 1)
```

The statements are in [`SunPi/Statement.lean`](SunPi/Statement.lean):

```lean
def SunConjecture_2_7_i : Prop :=
  ∀ n : ℕ, 4 < n → ∀ k : ℕ, 1 ≤ k → k ≤ n →
    (π ((k + 1) * n) : ℝ) ^ ((1 : ℝ) / (k + 1)) < (π (k * n) : ℝ) ^ ((1 : ℝ) / k)
def OeisA238165_ii : Prop :=
  ∀ n : ℕ, 4 < n →
    StrictAntiOn (fun k : ℕ => (π (k * n) : ℝ) ^ ((1 : ℝ) / k)) (Set.Icc 1 n)
def SunConjecture_2_14_ii : Prop :=
  ∀ n : ℕ, 3 ≤ n →
    (π ((n + 1) ^ 2) : ℝ) ^ ((1 : ℝ) / (n + 1)) < (π (n ^ 2) : ℝ) ^ ((1 : ℝ) / n)
def a (n : ℕ) : ℕ := (Nat.primesBelow (n ^ 2)).card
def OeisA038107_i : Prop :=
  StrictAntiOn (fun n : ℕ => (a n : ℝ) ^ ((1 : ℝ) / n)) (Set.Ici 3) ∧
    Tendsto (fun n : ℕ => (a n : ℝ) ^ ((1 : ℝ) / n)) atTop (𝓝 1)
```

## Tier and provenance

All four theorems are **tier D**: closed statements with no hypotheses, proved from Mathlib
alone. Nothing here imports riemann-hypothesis. The literature status is that of an open
conjecture for which we found no published proof; no label from `docs/LITERATURE_STATUS.md` is
claimed, and the label *new* awaits the owner's sign-off.

The statements were transcribed from Sun's paper (arXiv:1402.6641 v12, read 2026-11-26) and
from the OEIS comments (A238165, A038107, read the same day). Sun's paper form of 2.7(i) runs
`k` up to `n`, so it also compares `k = n` with `k = n + 1`; the OEIS form (`k = 1, …, n`) is the
weaker `OeisA238165_ii`, derived from it. formal-conjectures (clone `9097e2f`) has neither
statement. Its `FormalConjectures/OEIS/38107.lean` defines `OeisA38107.a`, copied here word for
word as `SunPi.a`, and states only Sun's 2015 conjecture on fractional parts.

## Axioms

Output of `#print axioms`, which `lake build SunPiChecks` also enforces
([`SunPiChecks/Axioms.lean`](SunPiChecks/Axioms.lean)):

```
'SunPi.sun_2_7_i' depends on axioms: [propext, Classical.choice, Quot.sound]
'SunPi.oeis_A238165_ii' depends on axioms: [propext, Classical.choice, Quot.sound]
'SunPi.sun_2_7_i_nat' depends on axioms: [propext, Classical.choice, Quot.sound]
'SunPi.sun_2_14_ii' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 SunPi.checkB_ok._native.native_decide.ax_1_1]
'SunPi.oeis_A038107_i' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 SunPi.checkB_ok._native.native_decide.ax_1_1]
'SunPi.sun_2_14_ii_nat' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 SunPi.checkB_ok._native.native_decide.ax_1_1]
'SunPi.Check.checkA_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
'SunPi.Check.checkB_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Conjecture 2.7(i) uses the standard three axioms only; its finite range is checked by the kernel
(`decide +kernel`, about 12 s). Conjecture 2.14(ii) uses one `native_decide`:
`SunPi.checkB_ok : checkB 3 4 697 = true`. It walks `n = 3, …, 699`, counting primes in each
`(n², (n+1)²]` by trial division (prime counting up to `700² = 490000`) and testing
`π((n+1)²)^n < π(n²)^{n+1}` in exact integers. It takes about 10 s. Its checker is proved sound
(`checkB_sound`, standard three axioms): `primeTD_iff` identifies the trial-division test with
`Nat.Prime`, and `primeCounting_add_cnt` identifies the count with `Nat.primeCounting`. The
kernel cannot do this range in reasonable time (`n ≤ 103` already took about 75 s).

## Proof outline

Write `P = π(X)` and `P + Δ = π(X + h)`.

1. **Reduction** (`pow_lt_of_mul_lt`, [`SunPi/Analytic.lean`](SunPi/Analytic.lean)). If
   `kΔ < P log P` then `(P + Δ)^k < P^{k+1}`, since `k log(1 + Δ/P) ≤ kΔ/P < log P`. Then
   `rpow_lt_of_pow_lt` turns `b^k < a^{k+1}` into `b^{1/(k+1)} < a^{1/k}`.
2. **Lower bound for `P log P`** (`PlogP_ge`). Mathlib gives `X log 2 ≤ ψ(X) ≤ π(X) log X` for
   `X ≥ 7`. With `Q = X log 2 / log X ≤ P`, `log log 2 ≥ −0.4428` and the tangent bound
   `log L ≤ L/2^i + i log 2 − 1`, one gets for `X ≥ 2^j`
   `P log P ≥ X·(log 2·(1 − 2^{−i}) − (i log 2 − 0.5572)/j)`.
3. **Upper bound for `Δ`** (Mathlib's `Nat.primeCounting_add_le`: primes above `a` are prime to
   `a`). For 2.7(i), `X = kn`, `h = n`, `a = 6`: `kΔ ≤ k·2(⌊n/6⌋ + 1) ≤ X/3 + 2k ≤ X(1/3 + 2/s)`
   when `n ≥ s`. For 2.14(ii), `X = n²`, `h = 2n + 1`, `a = 210`:
   `nΔ ≤ 48n(⌊(2n+1)/210⌋ + 1) ≤ X(96/210 + (48 + 48/210)/s)` when `n ≥ s`.
4. **Regions** ([`SunPi/Main.lean`](SunPi/Main.lean)). Step 2 beats step 3 when
   `coef(j, i) > main + add/s`; each instance is one `linarith` over Mathlib's nine-digit bounds
   for `log 2`. For 2.7(i) the regions `(j, s, i)` are `(6, 42, 2)`, `(7, 30, 2)`, `(8, 25, 2)`,
   `(9, 20, 3)`, `(10, 17, 3)`, `(11, 15, 3)`; for 2.14(ii) the single region `(18, 700, 4)`
   covers every `n ≥ 700` (margin `7·10⁻⁴`).
5. **Finite ranges** ([`SunPi/Check.lean`](SunPi/Check.lean)). What the regions leave for 2.7(i)
   is `5 ≤ n ≤ 63` with `kn < bndA n` (at most `kn < 8192`, in fact `(k+1)n ≤ 546`), done by
   `checkA_ok` in the kernel. For 2.14(ii) it is `3 ≤ n ≤ 699`, done by `checkB_ok`.
6. **OEIS forms**. `OeisA238165_ii` chains the steps of 2.7(i) along `[1, n]`. For A038107,
   `a n = π(n²)` for `n ≥ 2` (`a_eq`, as `n²` is not prime); the limit 1 follows by squeezing
   `1 ≤ a(n)^{1/n} ≤ (n^{1/n})²` with Mathlib's `tendsto_rpow_div`.

| File | Content |
| --- | --- |
| `SunPi/Statement.lean` | the fixed statements |
| `SunPi/Analytic.lean` | reduction, Chebyshev bound for `P log P`, the two region lemmas |
| `SunPi/Check.lean` | trial division, prime counting, the two loops and their soundness |
| `SunPi/Main.lean` | region constants, the finite checks, the headline theorems |
| `SunPiChecks/Axioms.lean` | `#guard_msgs` axiom allow-list |

## Independent recomputation

A C sieve to `4·10⁸` (run 2026-11-26, not part of the package) checked 2.7(i) for every
`5 ≤ n ≤ 19999` and every `k ≤ n` with `(k+1)n ≤ 4·10⁸` (about `2·10⁸` pairs), and 2.14(ii) for
every `3 ≤ n ≤ 19998`. The smallest margins `(k+1) log π(kn) − k log π((k+1)n)` are `0.5754`
(`n = 5, k = 2`) and `0.1699` (`n = 4`; `0.1699` also at `n = 3`).

## Deviations from the literature

None in the statements. The method has one feature worth recording. With the sharper bound
`π(x) ≥ x/log x` (Rosser–Schoenfeld, `x ≥ 17`) and the count of integers prime to 6, the
analytic argument would close 2.14(ii) from about `n = 14`. Mathlib has only Chebyshev's
constant `log 2`, and with it the count prime to 6 (density `2/3`) never closes 2.14(ii) in a
usable range, so we count integers prime to 210 instead and check `n ≤ 699` by computer.

## Building

```
lake build SunPi SunPiChecks
```

Lean `v4.36.0`, Mathlib `fc4f59e577feb1a4956671bc04ac18aaaf8cd842`, Mathlib only (packages from
the repository's shared `.lake/packages`). With Mathlib built, `SunPi.Main` takes about 40–60 s
wall on a loaded box: 12 s kernel check, 10 s `native_decide`.

## Unconditional version

No unconditional version is needed: the results are tier D and do not use RH.

## Literature and prior work

- Z.-W. Sun, *Problems on combinatorial properties of primes*, arXiv:1402.6641 (v12,
  2016-02-25); in M. Kaneko, S. Kanemitsu, J. Liu (eds.), *Number Theory: Plowing and Starring
  through High Wave Forms*, Ser. Number Theory Appl. 11, World Sci., 2015, pp. 169–187.
  Conjectures 2.7(i) and 2.14(ii), both dated 2014-02-17.
- OEIS A238165 (comment (ii)) and A038107 (Sun's comment of Feb 17 2014, part (i)).
- P. L. Chebyshev's bound in Mathlib's form `Chebyshev.psi_ge_of_seven_le`.

**Searches for a proof** (2026-11-26), none of which found one:

- arXiv and the web (web search for the two inequalities and "Sun conjecture π(kn)^{1/k}");
  Sun–Zhao, arXiv:2004.01080, concerns `π(kn)` being prime, not 2.7(i); Wang–Zhu,
  arXiv:1303.5595 (2013), proves other Sun monotonicity conjectures and predates these two.
- The OEIS entries A238165 and A038107: the conjectures stand as comments, with no note of a
  proof.
- formal-conjectures `9097e2f` (statements and `formal_proof` attributes) and its pull requests
  (`gh pr list --state all` for `238165`, `38107`, `pi(k*n)`): nothing.
- GitHub code search for `A238165`, `A038107`, `pi(k*n)^(1/k)`, `pi(n^2)^(1/n)`: only OEIS
  mirrors (joeis, loda) and this workspace's own scouting notes.
- MathOverflow, through web search: nothing found.
- The scouting report of 2026-11-26 (`docs/atlas/sweeps/2026-11-26/novel-oeis-lists.md`) lists
  the earlier searches (Exa, Zenodo, 1337isnot1337/solved-conjectures).

## Credits

Built with the [OpenHuman](https://github.com/tinyhumansai/openhuman) agents. Nothing is
vendored. The package uses only Mathlib (Apache-2.0). Licence: GPL v3 (`LICENSE`).
