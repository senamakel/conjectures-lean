# Mills' constant under RH in Lean

Mills (Bull. AMS 53, 1947) showed there is a real `A > 1` with `⌊A^(3^n)⌋` prime for every
`n ≥ 1`; the least such `A` is *Mills' constant*. Caldwell and Cheng (*Determining Mills'
constant and a note on Honaker's problem*, J. Integer Seq. 8 (2005), Art. 05.4.1) showed that
under the Riemann hypothesis it lies in `(1.3063778838, 1.3063778839)`: RH gives a prime between
`x³` and `(x+1)³` for all `x ≥ 2657` (via Schoenfeld's bound on `π(x) − li(x)`), so the greedy
sequence `2, 11, 1361, 2521008887, …` never gets stuck and its limit is a Mills number. The
lower bound needs no RH. Unconditionally, the constant is only known to exist (Mills) and to be
irrational (Saito, Mathematika 71, 2025).

```lean
-- Mills/Main.lean
theorem Mills.mills_lower_bound {A : ℝ} (hA : IsMinMills A) : (1.3063778838 : ℝ) < A

theorem Mills.mills_bounds_of_primeBetweenCubes {x₀ : ℕ} (h : PrimeBetweenCubes x₀)
    (hx : x₀ ≤ 2521008887) {A : ℝ} (hA : IsMinMills A) :
    A ∈ Set.Ioo (1.3063778838 : ℝ) 1.3063778839

theorem Mills.lowerBoundOfRH_of_primeBetweenCubes {x₀ : ℕ} (hx : x₀ ≤ 2521008887)
    (hRH : RiemannHypothesis → PrimeBetweenCubes x₀) : LowerBoundOfRH
```

with, in `Mills/Upper.lean`,

```lean
def PrimeBetweenCubes (x₀ : ℕ) : Prop :=
  ∀ x : ℕ, x₀ ≤ x → ∃ p : ℕ, p.Prime ∧ x ^ 3 < p ∧ p < (x + 1) ^ 3
```

## Tier and provenance

| Theorem | Tier | Hypothesis |
|---|---|---|
| `Mills.mills_lower_bound` | **D** | none |
| `Mills.exists_mills_lt` (a Mills number `< 1.3063778839` exists) | **C + H** | `PrimeBetweenCubes x₀`, `x₀ ≤ 2521008887` |
| `Mills.mills_bounds_of_primeBetweenCubes` (the full enclosure) | **C + H** | `PrimeBetweenCubes x₀`, `x₀ ≤ 2521008887` |
| `Mills.lowerBoundOfRH_of_primeBetweenCubes` | **C + H** | `RiemannHypothesis → PrimeBetweenCubes x₀` |

**The full result is not yet tier U.** The one named hypothesis, `PrimeBetweenCubes x₀`, is the
analytic input "a prime lies between `x³` and `(x+1)³` for all `x ≥ x₀`". It is not discharged
here. Caldwell–Cheng obtain it for `x₀ = 2657` from Schoenfeld's bound
`|π(x) − li(x)| < √x log x / (8π)` for `x ≥ 2657` under RH (their Lemma 5); that bound is being
formalised separately in `schoenfeld-rh`, which is not published yet, so this repository does
not depend on it (rule 7). When it lands, a short lemma (`li(b) − li(a) ≥ (b − a)/log b`
against twice the error term, at `a = x³`, `b = (x+1)³ − 1`; the inequality
`4π x² > 3 (x+1)^{3/2} log²(x+1)` holds with a wide margin already at `x = 2657`) turns it into
`RiemannHypothesis → PrimeBetweenCubes 2657`, and `Unconditional/` follows.

Why the erdos-985 toolkit does not discharge it directly: it proves the *Cesàro-weighted* sum
`Σ_{n<N} Λ(n)(1 − n/N) = N/2 + O(√N)` (kernel `1/(s(s+1))`, GRH, `bach_principal_of_GRH`).
Detecting a prime in an interval `(y, y + h)` from that needs a second difference, which gives
`h² > c·y^{3/2}`, i.e. `h ≫ y^{3/4}`. The interval here has length `≈ 3 y^{2/3}`, so the
smoothing loses too much. Closing the gap needs either the unsmoothed `ψ(y) − y = O(√y log² y)` (Schoenfeld's route) or
an explicit formula for a smooth weight of width `h ≈ y^{2/3}` whose Mellin transform decays
fast; more integrations of the kernel (`1/(s(s+1)(s+2))`, …) make it worse, not better, since
a `k`-th difference needs `h ≫ y^{1−1/(2k)}`. The toolkit has neither. It would also need GRH where
the target needs only RH: `bach_principal_of_GRH` takes `DirichletLNonvanishingRightOfHalf`.

### No range below `x₀` needs a direct check

The hypothesis is used only at the points `x = g n` with `n ≥ 3`, that is `x ≥ 2521008887`. The
first three steps `2 → 11 → 1361 → 2521008887` are verified directly in `Mills/Greedy.lean`
(`g_one`, `g_two`, `g_three`: the least prime above `2³ = 8` is `11`, above `11³ = 1331` is
`1361`, above `1361³ = 2521008881` is `2521008887`, by checking `3`, `30` and `6` integers).
So any `x₀ ≤ 2521008887` suffices, in particular Schoenfeld's `x₀ = 2657`, and the cubes between
`2657³` and `2521008887³` are never needed.

`IsMills` and `IsMinMills` are copied verbatim from
[formal-conjectures `Wikipedia/Mills.lean`](https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/Wikipedia/Mills.lean)
(commit `86a2f58a`), and `Mills.LowerBoundOfRH` in `Mills/Statement.lean` is its
`lower_bound_of_RH` as a proposition, with Mathlib's `RiemannHypothesis`. The main library does
not import riemann-hypothesis.

## Axioms

`lake env lean scripts/axioms.lean` (2026-11-24, build of branch `finality`):

```
'Mills.prime_2521008887' depends on axioms: [propext, Classical.choice, Quot.sound]
'Mills.g_three' depends on axioms: [propext, Classical.choice, Quot.sound]
'Mills.mills_lower_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
'Mills.exists_mills_lt' depends on axioms: [propext, Classical.choice, Quot.sound]
'Mills.mills_bounds_of_primeBetweenCubes' depends on axioms: [propext, Classical.choice, Quot.sound]
'Mills.lowerBoundOfRH_of_primeBetweenCubes' depends on axioms: [propext, Classical.choice, Quot.sound]
```

The standard three only: no `sorry`, no `native_decide`, no `axiom` declarations. The primality of
`2521008887` is a Lucas certificate (`5` is a primitive root, `2521008886 = 2·11·23·4982231`),
with the modular powers evaluated by `reduce_mod_char`.

## Proof outline

1. `Mills/Greedy.lean`: `g 0 = 2`, `g (n+1)` = least prime `≥ (g n)³` (exists unconditionally).
   `g_one`, `g_two`, `g_three` compute `11, 1361, 2521008887`.
2. Minimality, no RH (`g_le_floor`): if `⌊A^(3^n)⌋` is prime for all `n`, then
   `⌊A^(3^(n+1))⌋ ≥ ⌊A^(3^n)⌋³`, so by induction `⌊A^(3^(n+1))⌋ ≥ g n`. At `n = 3`,
   `A^81 ≥ 2521008887 > 1.3063778838^81` (`lower_bound`, a rational comparison by `norm_num`).
3. `Mills/Upper.lean`: from `PrimeBetweenCubes`, `g (n+1) < (g n + 1)³`, and strictly
   `g (n+1) + 1 < (g n + 1)³` since `(g n+1)³ − 1 = g n·(g n² + 3 g n + 3)` is composite.
   Hence `lo n = (g n)^{1/3^{n+1}}` increases, `hi n = (g n + 1)^{1/3^{n+1}}` decreases, and
   `lo n ≤ hi m` for all `n, m`.
4. The limit `A = sup lo n` satisfies `⌊A^(3^(n+1))⌋ = g n` (`floor_greedyLimit`), so it is a
   Mills number (`isMills_greedyLimit`), and `A^81 ≤ 2521008888 < 1.3063778839^81`.
5. `Mills/Main.lean`: the least Mills number `A` has `A ≤` this one and `A >` the lower bound.

## Layout

| File | Content |
|---|---|
| `Mills/Statement.lean` | `IsMills`, `IsMinMills` (verbatim), `LowerBoundOfRH` |
| `Mills/Greedy.lean` | greedy sequence, the four values, primality certificate, lower bound |
| `Mills/Upper.lean` | `PrimeBetweenCubes`, monotone enclosure, greedy limit is Mills |
| `Mills/Main.lean` | headline theorems |
| `scripts/axioms.lean` | `#print axioms` for the headline theorems |

## Deviations from the literature

None in the constants: the enclosure is exactly Caldwell–Cheng's. The only difference is that
the prime-between-cubes input is a named hypothesis rather than derived from Schoenfeld's bound.
The statement is stronger than needed in one respect: `PrimeBetweenCubes` is only used from
`x = 2521008887`, so `x₀` may be anything up to that.

## Building

Lean `v4.36.0`, Mathlib `fc4f59e5` (via erdos-985 `9538edb`).

```
lake exe cache get
lake build            # target `Mills`; the four modules take about 15 s once Mathlib and erdos-985 are built
```

(Building erdos-985 from its Mathlib cache takes about 2 minutes on 16 cores.)

## Unconditional version

None yet: `PrimeBetweenCubes` is not discharged (see above), so there is no `Unconditional/`
and no `scripts/check-unconditional.sh`. This will be added with the bridge from `schoenfeld-rh`,
together with the riemann-hypothesis table and caveat.

## Credits

No vendored files. The statements are from google-deepmind/formal-conjectures (Apache-2.0,
commit `86a2f58a`).
