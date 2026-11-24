# The average number of Goldbach representations under RH in Lean

With `Λ` the von Mangoldt function and `G(n) = Σ_{a+b=n} Λ(a)Λ(b)`, Lean proves

    |Σ_{n≤x} G(n) − x²/2| ≤ 4000·x^{3/2} log² x    for every real x ≥ 2.

`goldbach_average_sharp` and `goldbach_average` are proved unconditionally in Lean, from the
standard three axioms, with RH supplied by the certified proof in
[leanprover-community/riemann-hypothesis](https://github.com/leanprover-community/riemann-hypothesis).
The main library holds a complete Lean proof that RH implies the bound, with the explicit
constant `4000`, and hence `Σ_{n≤x} G(n) = x²/2 + O(x^{3/2+ε})` for every `ε > 0`.

**Literature status: RH-equivalent.** Fujii (*An additive problem of prime numbers*, Acta Arith.
58 (1991), 173-179) proved that RH implies `Σ_{n≤x} G(n) = x²/2 + O(x^{3/2})`, and in part II
(Proc. Japan Acad. 67A (1991), 248-252) gave the secondary term `−2 Σ_ρ x^{ρ+1}/(ρ(ρ+1))` with
error `O((x log x)^{4/3})`. Bhowmik–Schlage-Puchta (Nagoya Math. J. 200 (2010), 27-33) reduced
the error to `O(x log⁵ x)`, and Languasco–Zaccagnini (Proc. AMS 140 (2012), 795-804) and
Goldston–Yang to `O(x log³ x)`; the error is `Ω(x log log x)`. Granville (*Refinements of
Goldbach's conjecture, and the generalized Riemann hypothesis*, Funct. Approx. Comment. Math. 37
(2007), 159-173, Theorem 1A) stated that `Σ_{n≤x} G(n) = x²/2 + O(x^{3/2+o(1)})` is equivalent
to RH; his proof of the converse was incomplete and was finished by Bhowmik–Ruzsa (*Average
Goldbach and the Quasi-Riemann Hypothesis*, arXiv:1711.06442). The estimate is therefore RH in
another form. The literature's error term is `O(x^{3/2})` (Fujii); see "Deviations".

The proof here takes the direction RH ⇒ bound, following the argument noted in
Bhowmik–Schlage-Puchta's introduction: if `ψ(x) = x + O(f(x))` then
`Σ_{n≤x} G(n) = x²/2 + O(x f(x))`. The statement is about the average of `G(n)` and is
compatible with `G(n) = 0` at some even `n`, so it does not bear on Goldbach's conjecture itself.

```lean
theorem goldbach_average_sharp : GoldbachAverage.GoldbachAverageSharp 4000   -- Unconditional/
theorem goldbach_average : GoldbachAverage.GoldbachAverageBound             -- Unconditional/

theorem GoldbachAverage.goldbachAverageSharp_of_RH (hRH : RiemannHypothesis) :
    GoldbachAverage.GoldbachAverageSharp 4000

theorem GoldbachAverage.goldbachAverage_of_RH (hRH : RiemannHypothesis) :
    GoldbachAverage.GoldbachAverageBound
```

The targets, fixed in `GoldbachAverage/Statement.lean`:

```lean
noncomputable def goldbachWeight (n : ℕ) : ℝ :=
  ∑ p ∈ Finset.HasAntidiagonal.antidiagonal n, (Λ p.1 : ℝ) * (Λ p.2 : ℝ)

noncomputable def goldbachSum (x : ℝ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, goldbachWeight n

def GoldbachAverageBound : Prop :=
  ∀ ε : ℝ, 0 < ε →
    (fun x : ℝ => goldbachSum x - x ^ 2 / 2) =O[atTop] fun x : ℝ => x ^ ((3 : ℝ) / 2 + ε)

def GoldbachAverageSharp (C : ℝ) : Prop :=
  ∀ x : ℝ, 2 ≤ x →
    |goldbachSum x - x ^ 2 / 2| ≤ C * (x * Real.sqrt x * Real.log x ^ 2)
```

No formal-conjectures statement exists (searched 2026-11-24:
`FormalConjectures/Wikipedia/GoldbachConjecture.lean` is the only Goldbach file and has no von Mangoldt average), so these statements are written here.
`GoldbachAverageBound` is the target and follows from `GoldbachAverageSharp 4000`.

## Tier and provenance

| Theorem | Tier | Hypothesis |
|---|---|---|
| `GoldbachAverage.goldbachAverageSharp_of_RH` | C | `RiemannHypothesis` (Mathlib's statement) |
| `GoldbachAverage.goldbachAverage_of_RH` | C | `RiemannHypothesis` |
| `goldbach_average_sharp` (`Unconditional/`) | U | none; RH from riemann-hypothesis |
| `goldbach_average` (`Unconditional/`) | U | none; RH from riemann-hypothesis |

The only input from outside Mathlib is [schoenfeld-rh](https://github.com/senamakel/schoenfeld-rh)
(pinned at `14df2ce`), whose `Schoenfeld.psiBound_of_RH : PsiBound (1/8) 73.2` is
`|ψ(x) − x| < (1/8) √x log² x` for `x ≥ 73.2` under Mathlib's `RiemannHypothesis`.

## Axioms

Output of `scripts/check-axioms.sh` (`#print axioms` on each main-library theorem):

```
'GoldbachAverage.goldbachAverageSharp_of_RH' depends on axioms: [propext, Classical.choice, Quot.sound]
'GoldbachAverage.goldbachAverage_of_RH' depends on axioms: [propext, Classical.choice, Quot.sound]
```

No `native_decide`, no `sorry`, no `axiom` or `opaque` declarations.

## Proof outline

1. `GoldbachAverage/Sum.lean`: `S(N) = Σ_{a≤N} Λ(a) ψ(N−a)` (swap the double sum over
   `a + b ≤ N`), and `Σ_{a≤N} Λ(a)(N−a) = Σ_{k<N} ψ(k)` (induction on `N`).
2. `GoldbachAverage/Main.lean`, `abs_psi_sub_le`: for `k ≤ N`,
   `|ψ(k) − k| ≤ (1/8)√N log² N + 400`: Schoenfeld's bound from `k ≥ 73.2`, and
   `ψ(k) ≤ 5.4 k` (Mathlib's `psi_le_const_mul_self`) below.
3. `goldbach_sharp_nat`: writing `ψ(u) = u + e(u)`,
   `S(N) − N²/2 = −N/2 + Σ_{k<N} e(k) + Σ_a Λ(a) e(N−a)`, so
   `|S(N) − N²/2| ≤ N/2 + N·B + ψ(N)·B ≤ N/2 + 6.4 N B` with `B = (1/8)√N log² N + 400`,
   which is at most `3900 N^{3/2} log² N` for `N ≥ 2`.
4. `goldbachAverageSharp_of_RH`: pass from integer `N = ⌊x⌋` to real `x` (loses at most `x`),
   giving the constant `4000`.
5. `goldbachAverage_of_RH`: `log² x = o(x^ε)` (Mathlib's `isLittleO_log_rpow_rpow_atTop`).

## Layout

| File | Content |
|---|---|
| `GoldbachAverage/Statement.lean` | Fixed targets |
| `GoldbachAverage/Sum.lean` | Convolution identities |
| `GoldbachAverage/Main.lean` | The bounds under RH |
| `Unconditional/GoldbachAverageUnconditional.lean` | One-line discharge of RH |

## Deviations from the literature

The proved error term is `O(x^{3/2} log² x)`; Fujii's is `O(x^{3/2})`, and with the secondary term
`−2 Σ_ρ x^{ρ+1}/(ρ(ρ+1))` the literature reaches `O(x log³ x)` (Languasco–Zaccagnini,
Goldston–Yang). The secondary term is not proved here. The first-order estimate is what the
equivalence with RH needs for the direction RH ⇒ bound. The route is elementary and cannot go
below `x · √x`, because it uses `ψ(x) − x ≪ √x log² x` pointwise and gives up the oscillation of
the zero sum.

The constant `4000` is not optimised. It absorbs a crude bound of `400` on `|ψ(k) − k|` for
`k < 74` and the loss from real to integer `x`.

The converse (bound ⇒ RH, Granville 2007 and Bhowmik–Ruzsa) is not formalised.

## Building

Lean `v4.36.0`, Mathlib `fc4f59e5` (via erdos-985 `9538edb`), schoenfeld-rh `14df2ce`.

```bash
lake exe cache get
lake build            # target `GoldbachAverage`
scripts/check-axioms.sh
```

The modules of this library take about 20 s together once erdos-985 and schoenfeld-rh are
built (schoenfeld-rh alone is about 4.5 min wall on a cold build).

## Unconditional version

`Unconditional/GoldbachAverageUnconditional.lean` imports riemann-hypothesis and closes the RH
hypothesis with its `riemannHypothesis` in one line each:

| Theorem | Statement | Axioms |
|---|---|---|
| `goldbach_average_sharp` | `GoldbachAverageSharp 4000` | `propext`, `Classical.choice`, `Quot.sound` |
| `goldbach_average` | `GoldbachAverageBound` | `propext`, `Classical.choice`, `Quot.sound` |

Output of `scripts/check-unconditional.sh` on 2026-11-24 (commit `cbb3bf8`, riemann-hypothesis
`507a75d91d`):

```
'goldbach_average_sharp' depends on axioms: [propext, Classical.choice, Quot.sound]
'goldbach_average' depends on axioms: [propext, Classical.choice, Quot.sound]
```

```bash
scripts/check-unconditional.sh /path/to/riemann-hypothesis
```

The import needs about 93 GB of cache, about 19 GB of RAM and roughly 900k open files. Raise the
open-file limit first; on Linux `sudo prlimit --pid $$ --nofile=2000000:2000000`.

The riemann-hypothesis proof adds no axioms of its own. It was certified by the Lean FRO and the Mathlib Initiative on 2026-11-21, and independent kernels accept it (math.mit.edu/~drew/grh). This check links against the community build cache and does not repeat those kernel checks.

## Credits

No files are vendored. The lake dependencies are [erdos-985](https://github.com/senamakel/erdos-985)
(through schoenfeld-rh) and [schoenfeld-rh](https://github.com/senamakel/schoenfeld-rh).
