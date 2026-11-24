# The average number of Goldbach representations under RH in Lean

With `Λ` the von Mangoldt function and `G(n) = Σ_{a+b=n} Λ(a)Λ(b)`, Lean proves Fujii's theorem

    Σ_{n≤x} G(n) = x²/2 + O(x^{3/2}),

and the explicit bound

    |Σ_{n≤x} G(n) − x²/2| ≤ 4000·x^{3/2} log² x    for every real x ≥ 2.

`fujii_bound`, `fujii`, `goldbach_average_sharp` and `goldbach_average` are proved
unconditionally in Lean, from the standard three axioms, with RH supplied by the certified proof
in [leanprover-community/riemann-hypothesis](https://github.com/leanprover-community/riemann-hypothesis)
(L. Alpöge, 2026). The main library holds complete Lean proofs that RH implies each bound.

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
another form. Fujii's `O(x^{3/2})` is proved here with an existential constant; see "Deviations".

The proof here takes the direction RH ⇒ bound. The explicit bound follows the argument noted in
Bhowmik–Schlage-Puchta's introduction: if `ψ(x) = x + O(f(x))` then
`Σ_{n≤x} G(n) = x²/2 + O(x f(x))`. Fujii's bound comes from Cramér's mean square
`∫_1^X (ψ(t) − t)² dt ≪ X²` under RH (proved in [cramer-rh](https://github.com/senamakel/cramer-rh))
and the monotonicity of `ψ`, with no explicit formula (see "Proof outline"). The statement is about the average of `G(n)` and is
compatible with `G(n) = 0` at some even `n`, so it does not bear on Goldbach's conjecture itself.

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

Fujii's targets, fixed in `GoldbachAverage/Statement2.lean` (added in Round 6):

```lean
def FujiiBound : Prop :=
  ∃ C x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x → |goldbachSum x - x ^ 2 / 2| ≤ C * (x * Real.sqrt x)

def FujiiStatement : Prop :=
  (fun x : ℝ => goldbachSum x - x ^ 2 / 2) =O[atTop] fun x : ℝ => x ^ ((3 : ℝ) / 2)
```

The statement was checked against Languasco–Zaccagnini (arXiv:1011.3198), Theorem 1 and its
introduction, which credit the first result of this kind to Fujii (1991). Their
`R(n) = Σ_{h₁+h₂=n} Λ(h₁)Λ(h₂)` is `goldbachWeight n`, and because `Σ_ρ 1/|ρ(ρ+1)|` converges,
their Theorem 1 gives `Σ_{n≤N} R(n) = N²/2 + O(N^{3/2})` under RH. Fujii's paper itself was not
read.

## Tier and provenance

| Theorem | Tier | Hypothesis |
|---|---|---|
| `GoldbachAverage.fujii_of_RH` | C | `RiemannHypothesis` (Mathlib's statement) |
| `GoldbachAverage.fujiiStatement_of_RH` | C | `RiemannHypothesis` |
| `GoldbachAverage.fujiiBound_of_meanSquare` | H | `Cramer.CramerMeanSquare` (Cramér 1922; proved under RH in cramer-rh) |
| `fujii_bound`, `fujii` (`Unconditional/`) | U | none; RH from riemann-hypothesis |
| `GoldbachAverage.goldbachAverageSharp_of_RH` | C | `RiemannHypothesis` (Mathlib's statement) |
| `GoldbachAverage.goldbachAverage_of_RH` | C | `RiemannHypothesis` |
| `goldbach_average_sharp` (`Unconditional/`) | U | none; RH from riemann-hypothesis |
| `goldbach_average` (`Unconditional/`) | U | none; RH from riemann-hypothesis |

The inputs from outside Mathlib are [schoenfeld-rh](https://github.com/senamakel/schoenfeld-rh)
(pinned at `14df2ce`), whose `Schoenfeld.psiBound_of_RH : PsiBound (1/8) 73.2` is
`|ψ(x) − x| < (1/8) √x log² x` for `x ≥ 73.2` under Mathlib's `RiemannHypothesis`, and
[cramer-rh](https://github.com/senamakel/cramer-rh) (pinned at `1b5144f`, its `main`), whose
`Cramer.meanSquare_of_RH : CramerMeanSquare` is `∫_1^X (ψ(x) − x)² dx = O(X²)` under the same
hypothesis.

## Axioms

Output of `scripts/check-axioms.sh` (`#print axioms` on each main-library theorem):

```
'GoldbachAverage.goldbachAverageSharp_of_RH' depends on axioms: [propext, Classical.choice, Quot.sound]
'GoldbachAverage.goldbachAverage_of_RH' depends on axioms: [propext, Classical.choice, Quot.sound]
'GoldbachAverage.fujii_of_RH' depends on axioms: [propext, Classical.choice, Quot.sound]
'GoldbachAverage.fujiiStatement_of_RH' depends on axioms: [propext, Classical.choice, Quot.sound]
'GoldbachAverage.fujiiBound_of_meanSquare' depends on axioms: [propext, Classical.choice, Quot.sound]
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

Fujii's bound (`GoldbachAverage/Fujii.lean`), with `E(t) = ψ(t) − t` and `h = ⌊√N⌋`:

6. `sample`: `ψ` is nondecreasing, so `E(c) ≤ E(t) + h` for `t ∈ [c, c+h]` and
   `E(c) ≥ E(t) − h` for `t ∈ [c−h, c]`. Hence `h E(c)² ≤ 2 ∫_{c−h}^{c+h} E² + 2h³` for every
   real `c`. `sampleSum` sums this along a progression of step `h`:
   `h Σ_{j<K} E(s+jh)² ≤ 4 ∫_{s−h}^{s+Kh} E² + 2Kh³`.
7. `blocks_le`: cut `a ∈ [1, N]` into blocks `(jh, jh+h]`. On a block, `N − a` lies within `h`
   of both `N − jh` and `N − jh − h`, so `|E(N−a)| ≤ |E(N−jh)| + |E(N−jh−h)| + h`, and the block
   carries `Λ`-mass `ψ(jh+h) − ψ(jh) = h + E(jh+h) − E(jh)`. This replaces the pointwise bound
   `|E| ≪ √N log² N` (which costs `log² N`) by sampled values of `E`.
8. `fujii_nat_of_meanSquare`: `xy ≤ (x² + y²)/2` turns the block sum into four sampled sums
   of `E²` at step `h`, each `≤ (4/h) ∫_{−2h}^{N+2h} E² + 2Kh² ≪ N²/h`; the sum `Σ_{k<N} E(k)` is
   the same estimate at step `1`. With `∫_1^X E² ≤ C X²` this gives
   `|S(N) − N²/2| ≤ (688 + 468 C)·N^{3/2}` for `N ≥ max(4, X₀)`.
9. `fujiiBound_of_meanSquare`: pass from `N = ⌊x⌋` to real `x`. `fujii_of_RH` feeds it
   `Cramer.meanSquare_of_RH`.

## Layout

| File | Content |
|---|---|
| `GoldbachAverage/Statement.lean` | Fixed targets |
| `GoldbachAverage/Sum.lean` | Convolution identities |
| `GoldbachAverage/Main.lean` | The explicit `x^{3/2} log² x` bound under RH |
| `GoldbachAverage/Statement2.lean` | Fujii's targets |
| `GoldbachAverage/Fujii.lean` | Fujii's `O(x^{3/2})` from Cramér's mean square |
| `Unconditional/GoldbachAverageUnconditional.lean` | One-line discharge of RH |

## Deviations from the literature

Fujii's `O(x^{3/2})` is proved with an existential constant `688 + 468·C + 1`, where `C` is
the (non-explicit) constant of cramer-rh's `CramerMeanSquare`. The explicit theorem is the
weaker `GoldbachAverageSharp 4000` (`x^{3/2} log² x`, every `x ≥ 2`).

The secondary term `−2 Σ_ρ x^{ρ+1}/(ρ(ρ+1))` with error `O(x log³ x)` (Languasco–Zaccagnini,
Goldston–Yang; `O(x log⁵ x)` Bhowmik–Schlage-Puchta) is not proved. The mean-square route stops
at `x^{3/2}`: the term `Σ_{k<N} (ψ(k) − k)` is genuinely of that size, and identifying it with the
zero sum needs the explicit formula for `ψ₁`.

The constant `4000` is not optimised. It absorbs a crude bound of `400` on `|ψ(k) − k|` for
`k < 74` and the loss from real to integer `x`.

The converse (bound ⇒ RH, Granville 2007 and Bhowmik–Ruzsa) is not formalised.

## Building

Lean `v4.36.0`, Mathlib `fc4f59e5` (via erdos-985 `9538edb`), schoenfeld-rh `14df2ce`,
cramer-rh `1b5144f` (with erdos-233 `1ff9f39`).

```bash
lake exe cache get
lake build            # target `GoldbachAverage`
scripts/check-axioms.sh
```

`GoldbachAverage/Fujii.lean` takes about 2 min (123 s on a loaded box); the other modules about
20 s together, once the dependencies are built. Cold, schoenfeld-rh is about 4.5 min wall and
cramer-rh's `Cramer.MeanSquare.Main` (with erdos-233 and erdos-985) about 30 CPU-minutes.

## Unconditional version

`Unconditional/GoldbachAverageUnconditional.lean` imports riemann-hypothesis and closes the RH
hypothesis with its `riemannHypothesis` in one line each:

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
