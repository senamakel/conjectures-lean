# Fujii's average Goldbach bound under RH in Lean

With `Λ` the von Mangoldt function and `G(n) = Σ_{a+b=n} Λ(a)Λ(b)`, this project proves Fujii's
theorem

    Σ_{n≤x} G(n) = x²/2 + O(x^{3/2}).

`fujii_bound` and `fujii` are proved unconditionally in Lean from the standard three axioms, with
RH supplied by the certified proof in
[leanprover-community/riemann-hypothesis](https://github.com/leanprover-community/riemann-hypothesis)
(L. Alpöge, 2026). The main library holds a complete Lean proof that RH implies the bound
(`fujii_of_RH`), following A. Fujii, *An additive problem of prime numbers*, Acta Arith. 58
(1991), 173-179. Granville (*Refinements of Goldbach's conjecture, and the generalized Riemann
hypothesis*, Funct. Approx. Comment. Math. 37 (2007), 159-173, Theorem 1A) stated that
`Σ_{n≤x} G(n) = x²/2 + O(x^{3/2+o(1)})` is equivalent to RH, with the converse completed by
Bhowmik and Ruzsa (*Average Goldbach and the Quasi-Riemann Hypothesis*, arXiv:1711.06442).
Literature status: **RH-equivalent**, so the estimate is RH in another form.

The project also proves an explicit form with a logarithmic loss,
`|Σ_{n≤x} G(n) − x²/2| ≤ 4000·x^{3/2} log² x` for every real `x ≥ 2`, and the `x^{3/2+ε}` form
that Granville states.

```lean
theorem fujii_bound : GoldbachAverage.FujiiBound                             -- Unconditional/
theorem fujii : GoldbachAverage.FujiiStatement                               -- Unconditional/
theorem goldbach_average_sharp : GoldbachAverage.GoldbachAverageSharp 4000   -- Unconditional/
theorem goldbach_average : GoldbachAverage.GoldbachAverageBound             -- Unconditional/

theorem GoldbachAverage.fujii_of_RH (hRH : RiemannHypothesis) : GoldbachAverage.FujiiBound

theorem GoldbachAverage.fujiiStatement_of_RH (hRH : RiemannHypothesis) :
    GoldbachAverage.FujiiStatement

theorem GoldbachAverage.fujiiBound_of_meanSquare (h : Cramer.CramerMeanSquare) :
    GoldbachAverage.FujiiBound

theorem GoldbachAverage.goldbachAverageSharp_of_RH (hRH : RiemannHypothesis) :
    GoldbachAverage.GoldbachAverageSharp 4000

theorem GoldbachAverage.goldbachAverage_of_RH (hRH : RiemannHypothesis) :
    GoldbachAverage.GoldbachAverageBound
```

Fujii's targets, fixed in `GoldbachAverage/Statement2.lean`:

```lean
def FujiiBound : Prop :=
  ∃ C x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x → |goldbachSum x - x ^ 2 / 2| ≤ C * (x * Real.sqrt x)

def FujiiStatement : Prop :=
  (fun x : ℝ => goldbachSum x - x ^ 2 / 2) =O[atTop] fun x : ℝ => x ^ ((3 : ℝ) / 2)
```

The definitions they use, and the `x^{3/2+ε}` and explicit targets, fixed in
`GoldbachAverage/Statement.lean`:

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

## Tier and provenance

| Theorem | Tier | Hypothesis |
|---|---|---|
| `fujii_bound`, `fujii` (`Unconditional/`) | U | none; RH from riemann-hypothesis |
| `GoldbachAverage.fujii_of_RH` | C | `RiemannHypothesis` (Mathlib's statement) |
| `GoldbachAverage.fujiiStatement_of_RH` | C | `RiemannHypothesis` |
| `GoldbachAverage.fujiiBound_of_meanSquare` | H | `Cramer.CramerMeanSquare` (Cramér 1922; proved under RH in cramer-rh) |
| `goldbach_average_sharp`, `goldbach_average` (`Unconditional/`) | U | none; RH from riemann-hypothesis |
| `GoldbachAverage.goldbachAverageSharp_of_RH` | C | `RiemannHypothesis` (Mathlib's statement) |
| `GoldbachAverage.goldbachAverage_of_RH` | C | `RiemannHypothesis` |

formal-conjectures has no statement for this average (searched 2026-11-24:
`FormalConjectures/Wikipedia/GoldbachConjecture.lean` is the only Goldbach file and has no von
Mangoldt average), so the statements are written here. `GoldbachAverageBound` follows from
`GoldbachAverageSharp 4000`.

Fujii's statement was checked against Languasco and Zaccagnini (arXiv:1011.3198), Theorem 1 and
its introduction, which credit the first result of this kind to Fujii (1991). Their
`R(n) = Σ_{h₁+h₂=n} Λ(h₁)Λ(h₂)` is `goldbachWeight n`, and because `Σ_ρ 1/|ρ(ρ+1)|` converges,
their Theorem 1 gives `Σ_{n≤N} R(n) = N²/2 + O(N^{3/2})` under RH. Fujii's paper was read
through that source.

Later work sharpens the error term under RH. Fujii's part II (Proc. Japan Acad. 67A (1991),
248-252) gave the secondary term `−2 Σ_ρ x^{ρ+1}/(ρ(ρ+1))` with error `O((x log x)^{4/3})`.
Bhowmik and Schlage-Puchta (Nagoya Math. J. 200 (2010), 27-33) reduced the error to
`O(x log⁵ x)`, and Languasco and Zaccagnini (Proc. AMS 140 (2012), 795-804) and Goldston and Yang
to `O(x log³ x)`. The error is `Ω(x log log x)`.

The inputs from outside Mathlib are [schoenfeld-rh](https://github.com/senamakel/schoenfeld-rh)
(pinned at `14df2ce`), whose `Schoenfeld.psiBound_of_RH : PsiBound (1/8) 73.2` is
`|ψ(x) − x| < (1/8) √x log² x` for `x ≥ 73.2` under Mathlib's `RiemannHypothesis`, and
[cramer-rh](https://github.com/senamakel/cramer-rh) (pinned at `1b5144f`), whose
`Cramer.meanSquare_of_RH : CramerMeanSquare` is `∫_1^X (ψ(x) − x)² dx = O(X²)` under the same
hypothesis.

The theorems concern the average of `G(n)`. They allow `G(n) = 0` at some even `n`, so they make
no statement about Goldbach's conjecture itself.

## Axioms

Output of `scripts/check-axioms.sh` (`#print axioms` on each main-library theorem):

```
'GoldbachAverage.goldbachAverageSharp_of_RH' depends on axioms: [propext, Classical.choice, Quot.sound]
'GoldbachAverage.goldbachAverage_of_RH' depends on axioms: [propext, Classical.choice, Quot.sound]
'GoldbachAverage.fujii_of_RH' depends on axioms: [propext, Classical.choice, Quot.sound]
'GoldbachAverage.fujiiStatement_of_RH' depends on axioms: [propext, Classical.choice, Quot.sound]
'GoldbachAverage.fujiiBound_of_meanSquare' depends on axioms: [propext, Classical.choice, Quot.sound]
```

The repository has no `native_decide`, no `sorry` and no `axiom` or `opaque` declarations.

## Proof outline

Fujii's bound comes from Cramér's mean square `∫_1^X (ψ(t) − t)² dt ≪ X²` under RH and the
monotonicity of `ψ`, with no explicit formula. Write `E(t) = ψ(t) − t` and `h = ⌊√N⌋`.

1. `GoldbachAverage/Sum.lean`: `S(N) = Σ_{a≤N} Λ(a) ψ(N−a)` (swap the double sum over
   `a + b ≤ N`), and `Σ_{a≤N} Λ(a)(N−a) = Σ_{k<N} ψ(k)` (induction on `N`).
2. `GoldbachAverage/Fujii.lean`, `sample`: `ψ` is nondecreasing, so `E(c) ≤ E(t) + h` for
   `t ∈ [c, c+h]` and `E(c) ≥ E(t) − h` for `t ∈ [c−h, c]`. Hence
   `h E(c)² ≤ 2 ∫_{c−h}^{c+h} E² + 2h³` for every real `c`. `sampleSum` sums this along a
   progression of step `h`: `h Σ_{j<K} E(s+jh)² ≤ 4 ∫_{s−h}^{s+Kh} E² + 2Kh³`.
3. `blocks_le`: cut `a ∈ [1, N]` into blocks `(jh, jh+h]`. On a block, `N − a` lies within `h`
   of both `N − jh` and `N − jh − h`, so `|E(N−a)| ≤ |E(N−jh)| + |E(N−jh−h)| + h`, and the block
   carries `Λ`-mass `ψ(jh+h) − ψ(jh) = h + E(jh+h) − E(jh)`. Sampled values of `E` replace the
   pointwise bound `|E| ≪ √N log² N`, which would cost a factor `log² N`.
4. `fujii_nat_of_meanSquare`: `xy ≤ (x² + y²)/2` turns the block sum into four sampled sums of
   `E²` at step `h`, each `≤ (4/h) ∫_{−2h}^{N+2h} E² + 2Kh² ≪ N²/h`. The sum `Σ_{k<N} E(k)` is the
   same estimate at step `1`. With `∫_1^X E² ≤ C X²` this gives
   `|S(N) − N²/2| ≤ (688 + 468 C)·N^{3/2}` for `N ≥ max(4, X₀)`.
5. `fujiiBound_of_meanSquare`: pass from `N = ⌊x⌋` to real `x`. `fujii_of_RH` feeds it
   `Cramer.meanSquare_of_RH`, and `fujiiStatement_of_RH` restates it with `=O[atTop]`.

The explicit bound (`GoldbachAverage/Main.lean`) follows the argument in the introduction of
Bhowmik and Schlage-Puchta: if `ψ(x) = x + O(f(x))` then `Σ_{n≤x} G(n) = x²/2 + O(x f(x))`.

6. `abs_psi_sub_le`: for `k ≤ N`, `|ψ(k) − k| ≤ (1/8)√N log² N + 400`, from Schoenfeld's bound
   for `k ≥ 73.2` and `ψ(k) ≤ 5.4 k` (Mathlib's `psi_le_const_mul_self`) below.
7. `goldbach_sharp_nat`: writing `ψ(u) = u + e(u)`,
   `S(N) − N²/2 = −N/2 + Σ_{k<N} e(k) + Σ_a Λ(a) e(N−a)`, so
   `|S(N) − N²/2| ≤ N/2 + N·B + ψ(N)·B ≤ N/2 + 6.4 N B` with `B = (1/8)√N log² N + 400`,
   which is at most `3900 N^{3/2} log² N` for `N ≥ 2`.
8. `goldbachAverageSharp_of_RH`: pass from integer `N = ⌊x⌋` to real `x` (loses at most `x`),
   giving the constant `4000`.
9. `goldbachAverage_of_RH`: `log² x = o(x^ε)` (Mathlib's `isLittleO_log_rpow_rpow_atTop`).

## Layout

| File | Content |
|---|---|
| `GoldbachAverage/Statement.lean` | `G(n)`, `S(x)`, the `x^{3/2+ε}` and explicit targets |
| `GoldbachAverage/Statement2.lean` | Fujii's targets |
| `GoldbachAverage/Sum.lean` | Convolution identities |
| `GoldbachAverage/Fujii.lean` | Fujii's `O(x^{3/2})` from Cramér's mean square |
| `GoldbachAverage/Main.lean` | The explicit `x^{3/2} log² x` bound under RH |
| `Unconditional/GoldbachAverageUnconditional.lean` | One-line discharge of RH |

## Deviations from the literature

The constant in Fujii's bound is existential: `688 + 468·C + 1`, where `C` is the constant of
cramer-rh's `CramerMeanSquare`, which is not explicit. The explicit theorem is
`GoldbachAverageSharp 4000`, with an extra factor `log² x`. The constant `4000` absorbs a crude
bound of `400` on `|ψ(k) − k|` for `k < 74` and the loss from real to integer `x`.

The secondary term `−2 Σ_ρ x^{ρ+1}/(ρ(ρ+1))` with error `O(x log³ x)` (Languasco and Zaccagnini,
Goldston and Yang) is not proved. The mean-square route stops at `x^{3/2}`: the term
`Σ_{k<N} (ψ(k) − k)` is of that size, and identifying it with the zero sum needs the explicit
formula for `ψ₁`.

Only the direction RH ⇒ bound is formalised. The converse (Granville 2007, Bhowmik and Ruzsa)
is not.

## Building

Lean `v4.36.0`, Mathlib `fc4f59e5` (via erdos-985 `9538edb`), schoenfeld-rh `14df2ce`,
cramer-rh `1b5144f` (with erdos-233 `1ff9f39`).

```bash
lake exe cache get
lake build            # target `GoldbachAverage`
scripts/check-axioms.sh
```

`GoldbachAverage/Fujii.lean` takes about 2 min (123 s on a loaded box); the other modules take
about 20 s together once the dependencies are built. From cold, schoenfeld-rh takes about 4.5 min
wall and cramer-rh's `Cramer.MeanSquare.Main` (with erdos-233 and erdos-985) about 30
CPU-minutes.

## Unconditional version

`Unconditional/GoldbachAverageUnconditional.lean` imports riemann-hypothesis and closes the RH
hypothesis with its `riemannHypothesis`, one line per theorem:

| Theorem | Statement | Axioms |
|---|---|---|
| `fujii_bound` | `FujiiBound` | `propext`, `Classical.choice`, `Quot.sound` |
| `fujii` | `FujiiStatement` | `propext`, `Classical.choice`, `Quot.sound` |
| `goldbach_average_sharp` | `GoldbachAverageSharp 4000` | `propext`, `Classical.choice`, `Quot.sound` |
| `goldbach_average` | `GoldbachAverageBound` | `propext`, `Classical.choice`, `Quot.sound` |

Output of `scripts/check-unconditional.sh` on 2026-11-24 (commit `0903f33`, riemann-hypothesis
`507a75d91d`, 29.7 min wall on a loaded box, exit 0):

```
'goldbach_average_sharp' depends on axioms: [propext, Classical.choice, Quot.sound]
'goldbach_average' depends on axioms: [propext, Classical.choice, Quot.sound]
'fujii_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
'fujii' depends on axioms: [propext, Classical.choice, Quot.sound]
```

```bash
scripts/check-unconditional.sh /path/to/riemann-hypothesis
```

The import needs about 93 GB of cache, about 19 GB of RAM and roughly 900k open files. Raise the
open-file limit first; on Linux `sudo prlimit --pid $$ --nofile=2000000:2000000`.

The riemann-hypothesis proof adds no axioms of its own. It was certified by the Lean FRO and the Mathlib Initiative on 2026-11-21, and independent kernels accept it (math.mit.edu/~drew/grh). This check links against the community build cache and does not repeat those kernel checks.

## Credits

No files are vendored. The lake dependencies are [erdos-985](https://github.com/senamakel/erdos-985)
and [erdos-233](https://github.com/senamakel/erdos-233) (through schoenfeld-rh and cramer-rh),
[schoenfeld-rh](https://github.com/senamakel/schoenfeld-rh) and
[cramer-rh](https://github.com/senamakel/cramer-rh).
