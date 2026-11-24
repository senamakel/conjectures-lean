# Mills' constant under RH in Lean

Mills (Bull. AMS 53, 1947) showed there is a real `A > 1` with `⌊A^(3^n)⌋` prime for every
`n ≥ 1`; the least such `A` is *Mills' constant*. Caldwell and Cheng (*Determining Mills'
constant and a note on Honaker's problem*, J. Integer Seq. 8 (2005), Art. 05.4.1) showed that
under the Riemann hypothesis it lies in `(1.3063778838, 1.3063778839)`: RH gives a prime between
`x³` and `(x+1)³` for all large `x`, so the greedy sequence `2, 11, 1361, 2521008887, …` never
gets stuck and its limit is a Mills number.

**Literature status.** The enclosure is an *RH-consequence* (Caldwell–Cheng 2005; listed as open
in formal-conjectures; it follows from RH). The lower bound `A > 1.3063778838` is *known*
unconditionally (Caldwell–Cheng). The main library is a complete Lean proof that RH implies the
enclosure, following Caldwell–Cheng, with a prime between consecutive cubes from `x₀ = 10^9`
and the primality of 2521008887 checked by a Lucas certificate. `Unconditional/` proves the
enclosure unconditionally in Lean, with RH supplied by the certified proof in
leanprover-community/riemann-hypothesis. Before the 2026 proof of RH only existence (Mills) and
irrationality (Saito, Mathematika 71, 2025) were known.

```lean
-- Mills/Final.lean
theorem Mills.lower_bound_of_RH : LowerBoundOfRH   -- RiemannHypothesis → ∀ {A}, IsMinMills A → A ∈ Set.Ioo 1.3063778838 1.3063778839

theorem Mills.mills_bounds_of_RH (hRH : RiemannHypothesis) {A : ℝ} (hA : IsMinMills A) :
    A ∈ Set.Ioo (1.3063778838 : ℝ) 1.3063778839

-- Mills/Cubes.lean
theorem Mills.primeBetweenCubes_of_RH (hRH : RiemannHypothesis) : PrimeBetweenCubes (10 ^ 9)

-- Mills/Main.lean (no hypothesis at all)
theorem Mills.mills_lower_bound {A : ℝ} (hA : IsMinMills A) : (1.3063778838 : ℝ) < A

-- Mills/Upper.lean
def PrimeBetweenCubes (x₀ : ℕ) : Prop :=
  ∀ x : ℕ, x₀ ≤ x → ∃ p : ℕ, p.Prime ∧ x ^ 3 < p ∧ p < (x + 1) ^ 3
```

## Tier and provenance

| Theorem | Tier | Hypothesis |
|---|---|---|
| `Mills.mills_lower_bound` | **D** | none |
| `Mills.primeBetweenCubes_of_RH` | **C** | `RiemannHypothesis` (Mathlib's statement) |
| `Mills.lower_bound_of_RH`, `Mills.mills_bounds_of_RH` | **C** | `RiemannHypothesis` |
| `Mills.mills_bounds_of_primeBetweenCubes` (the reduction) | C + H | `PrimeBetweenCubes x₀`, `x₀ ≤ 2521008887` |
| `mills_constant_bounds_unconditional` (`Unconditional/`) | **U** | none; RH from riemann-hypothesis |

`PrimeBetweenCubes x₀` is the analytic input "a prime lies between `x³` and `(x+1)³` for all
`x ≥ x₀`". It is proved from RH for `x₀ = 10^9` in `Mills/Cubes.lean`, using
`Schoenfeld.thetaBound_of_RH : ThetaBound (1/4) 599` from
[`schoenfeld-rh`](https://github.com/senamakel/schoenfeld-rh) (rev `14df2ce`):
under RH, `|θ(y) − y| < √y log² y / 4` for `y ≥ 599`. This is a weaker constant than
Schoenfeld's `1/(8π)`, which is why Caldwell–Cheng's `x₀ = 2657` is replaced by `10^9` (any
`x₀ ≤ 2521008887` is enough, see below). The argument: a prime in `(a, b]` exists when
`θ(b) > θ(a)`; with `a = x³`, `b = x³ + 3x² + 3x = (x+1)³ − 1` the bound gives `θ(b) − θ(a) > 0`
as soon as `3x² + 3x > ½ √b log² b`. Putting `t = (x+1)^{1/8}` (so `√b ≤ t¹²`, `log b ≤ 24 t`)
this reduces to `3(t⁸ − 1)² > 288 t¹⁴`, true for `t ≥ 13`, i.e. `x ≥ 10^9`.

### No range below `x₀` needs a direct check

`PrimeBetweenCubes` is used only at the points `x = g n` with `n ≥ 3`, that is `x ≥ 2521008887`. The
first three steps `2 → 11 → 1361 → 2521008887` are verified directly in `Mills/Greedy.lean`
(`g_one`, `g_two`, `g_three`: the least prime above `2³ = 8` is `11`, above `11³ = 1331` is
`1361`, above `1361³ = 2521008881` is `2521008887`, by checking `3`, `30` and `6` integers).
So any `x₀ ≤ 2521008887` suffices, in particular `x₀ = 10^9` (and Caldwell–Cheng's `2657`), and the cubes between `x₀³` and
`2521008887³` are never needed.

`IsMills` and `IsMinMills` are copied verbatim from
[formal-conjectures `Wikipedia/Mills.lean`](https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/Wikipedia/Mills.lean)
(commit `86a2f58a`), and `Mills.LowerBoundOfRH` in `Mills/Statement.lean` is its
`lower_bound_of_RH` as a proposition, with Mathlib's `RiemannHypothesis`. The main library does
not import riemann-hypothesis.

## Axioms

`lake env lean scripts/axioms.lean` (2026-11-24, branch `finality`):

```
'Mills.prime_2521008887' depends on axioms: [propext, Classical.choice, Quot.sound]
'Mills.g_three' depends on axioms: [propext, Classical.choice, Quot.sound]
'Mills.mills_lower_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
'Mills.exists_mills_lt' depends on axioms: [propext, Classical.choice, Quot.sound]
'Mills.mills_bounds_of_primeBetweenCubes' depends on axioms: [propext, Classical.choice, Quot.sound]
'Mills.lowerBoundOfRH_of_primeBetweenCubes' depends on axioms: [propext, Classical.choice, Quot.sound]
'Mills.primeBetweenCubes_of_RH' depends on axioms: [propext, Classical.choice, Quot.sound]
'Mills.lower_bound_of_RH' depends on axioms: [propext, Classical.choice, Quot.sound]
'Mills.mills_bounds_of_RH' depends on axioms: [propext, Classical.choice, Quot.sound]
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
| `Mills/Main.lean` | reduction to `PrimeBetweenCubes`, lower bound |
| `Mills/Cubes.lean` | `PrimeBetweenCubes (10^9)` from RH via Schoenfeld's θ bound |
| `Mills/Final.lean` | `lower_bound_of_RH`, `mills_bounds_of_RH` |
| `Unconditional/MillsUnconditional.lean` | one-line discharge of RH from riemann-hypothesis |
| `scripts/check-unconditional.sh` | builds and checks the unconditional file |
| `scripts/axioms.lean` | `#print axioms` for the headline theorems |

## Deviations from the literature

None in the constants: the enclosure is exactly Caldwell–Cheng's. The prime-between-cubes input
comes from the θ bound with constant `1/4` (`schoenfeld-rh`), not Schoenfeld's `1/(8π)`, so the
threshold is `10^9` rather than `2657`. That is harmless: `PrimeBetweenCubes` is only used from
`x = 2521008887`, so any `x₀` up to that works.

## Building

Lean `v4.36.0`, Mathlib `fc4f59e5` (via erdos-985 `9538edb`).

```
lake exe cache get
lake build            # target `Mills`; the four modules take about 15 s once Mathlib and erdos-985 are built
```

`Schoenfeld` is a lake dependency (`schoenfeld-rh` rev `14df2ce`); with it a cold build adds about 2.5 minutes.

(Building erdos-985 from its Mathlib cache takes about 2 minutes on 16 cores.)

## Unconditional version

| Theorem | Statement | Axioms |
|---|---|---|
| `mills_constant_bounds_unconditional` | the least Mills number lies in `(1.3063778838, 1.3063778839)` | `[propext, Classical.choice, Quot.sound]` |

`#print axioms` output (2026-11-24, from `scripts/check-unconditional.sh`):

```
'mills_constant_bounds_unconditional' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Checked against riemann-hypothesis commit `507a75d91d` with
`scripts/check-unconditional.sh /path/to/riemann-hypothesis` (needs about 93 GB of cache, about
19 GB of RAM and a limit of roughly 900k open files). The riemann-hypothesis proof adds no axioms of its own. It was certified by the Lean FRO and the Mathlib Initiative on 2026-11-21, and independent kernels accept it (math.mit.edu/~drew/grh). This check links against the community build cache and does not repeat those kernel checks.

## Credits

No vendored files in this repository (the Schoenfeld bounds come from the `schoenfeld-rh` dependency). The statements are from google-deepmind/formal-conjectures (Apache-2.0,
commit `86a2f58a`).
