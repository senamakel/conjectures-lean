# Pólya's conjecture and von Sterneck's conjecture are false, in Lean

Pólya (1919) conjectured that the summatory Liouville function `L(n) = Σ_{k≤n} λ(k)` satisfies
`L(n) ≤ 0` for every `n ≥ 2`. This package proves in Lean that `L(906150257) = 1`, so the
conjecture is false. It also proves `M(7725038629) = 43947` for the Mertens function
`M(x) = Σ_{k≤x} μ(k)`. Since `4 · 43947² = 7725355236 > 7725038629`, this refutes von Sterneck's
conjecture `|M(x)| < ½√x` for `x > 200`. Both refutations are *known* (route c/e of the
refutation lane in `AGENTS.md`). Haselgrove (1958) disproved Pólya's conjecture without giving a
witness, and Tanaka (1980) found `906150257`, the smallest counterexample. Neubauer (1963) found
the first counterexamples to von Sterneck's conjecture, and Cohen and Dress (1979) found
`7725038629`, the smallest. Lean checks every step from Mathlib's `ArithmeticFunction.liouville`
and `ArithmeticFunction.moebius`, using one documented `native_decide` per value. Its checker is
proved sound.

## Headline theorems

```lean
theorem Polya.liouvilleSum_906150257 : liouvilleSum 906150257 = 1
theorem Polya.polya_conjecture_false : ¬ PolyaConjecture

theorem Polya.mertens_7725038629 : mertens 7725038629 = 43947
theorem Polya.vonSterneck_conjecture_false : ¬ VonSterneckConjecture
theorem Polya.vonSterneck_conjecture_int_false : ¬ VonSterneckConjectureInt
```

The statements are in [`Polya/Statement.lean`](Polya/Statement.lean):

```lean
def liouvilleSum (n : ℕ) : ℤ := ∑ k ∈ Finset.Icc 1 n, ArithmeticFunction.liouville k
def mertens (x : ℕ) : ℤ := ∑ k ∈ Finset.Icc 1 x, ArithmeticFunction.moebius k
def PolyaConjecture : Prop := ∀ n : ℕ, 2 ≤ n → liouvilleSum n ≤ 0
def VonSterneckConjecture : Prop := ∀ x : ℕ, 200 < x → |(mertens x : ℝ)| < Real.sqrt x / 2
def VonSterneckConjectureInt : Prop := ∀ x : ℕ, 200 < x → 4 * mertens x ^ 2 < x
```

## Tier and provenance

All five theorems are **tier D**: they are closed statements with no hypotheses, and nothing
here imports riemann-hypothesis. The literature label is *known*.

formal-conjectures has no statement of either conjecture. At `9097e2f` we searched for Pólya,
Liouville, Sterneck, `906150257` and `7725038629`. The only Liouville statements there are the
Chowla conjectures. So the statements were written here, following Pólya's wording: `n ≥ 2`,
with `λ(1) = 1`, so that `L(1) = 1` is excluded. The summation style is that of formal-conjectures'
`Wikipedia/ChowlaLiouvilleConjecture.lean`. Von Sterneck's inequality is stated twice, once with
the real square root as he wrote it and once squared in integers.

We prove that the conjectures fail at these points. We do **not** prove that `906150257` and
`7725038629` are the least counterexamples. Minimality is the content of Tanaka's and
Cohen–Dress's searches, and it is not formalised here.

## Axioms

Output of `#print axioms`, which `lake build PolyaChecks` also enforces
([`PolyaChecks/Axioms.lean`](PolyaChecks/Axioms.lean)):

```
'Polya.polya_conjecture_false' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Polya.Check.liouville_906150257_check._native.native_decide.ax_1_1]
'Polya.liouvilleSum_906150257' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Polya.Check.liouville_906150257_check._native.native_decide.ax_1_1]
'Polya.vonSterneck_conjecture_false' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Polya.Check.mertens_7725038629_check._native.native_decide.ax_1_1]
'Polya.vonSterneck_conjecture_int_false' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Polya.Check.mertens_7725038629_check._native.native_decide.ax_1_1]
'Polya.mertens_7725038629' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Polya.Check.mertens_7725038629_check._native.native_decide.ax_1_1]
```

There are two `native_decide`s, one for each value:

- `Polya.Check.liouville_906150257_check : runLiouville 906150257 1 = true`. It fills tables of
  `M` at the 60,203 points of `V` (all `y ≤ 30102` and every `⌊906150257/a⌋ > 30102`). It checks
  `Σ_{k≤y} M(⌊y/k⌋) = 1` at each of them by block sums, then adds up `M(⌊906150257/d²⌋)` for
  `d ≤ 30102`. The module takes about 23 s wall and 2.5 GB of RAM.
- `Polya.Check.mertens_7725038629_check : runMertens 7725038629 43947 = true`. It runs the same
  check on the 175,783 points of `V` for `X = 7725038629` (`T = 87892`), then reads off
  `M(X)`. The module takes 110 to 130 s wall on a loaded box, with 2.5 GB of RAM.

Both are evaluated by Lean's IR interpreter, since the module is not precompiled. The soundness theorems
`runLiouville_sound` and `runMertens_sound` use only the standard three axioms.

## Proof outline

1. **Identities** ([`Polya/Identities.lean`](Polya/Identities.lean)).
   - `sum_mertens_div`: `Σ_{n=1}^{x} M(⌊x/n⌋) = 1` for `x ≥ 1`. It follows from `ζ * μ = 1`
     (Mathlib's `coe_zeta_mul_moebius`) and `sum_Ioc_mul_eq_sum_sum`.
   - `liouville_mul_zeta`: `λ * ζ = 𝟙_□`, where `𝟙_□` is the indicator of the nonzero squares.
     Both sides are multiplicative. On a prime power, `Σ_{j≤i} (−1)^j = [i even]`, and `p^i` is a
     square exactly when `i` is even.
   - From these, `λ = 𝟙_□ * μ`, and `liouvilleSum_eq_sum_mertens` gives
     `L(x) = Σ_{d=1}^{⌊√x⌋} M(⌊x/d²⌋)`.
2. **Checker** ([`Polya/Check.lean`](Polya/Check.lean)).
   - `blockSum f x n` computes `Σ_{k=n}^{x} f(⌊x/k⌋)` in `O(√x)` steps. It groups the blocks
     `[n, ⌊x/⌊x/n⌋⌋]`, on which `⌊x/k⌋` is constant (`blockSum_eq`).
   - `tablesOK` checks the identity of step 1 at every point of
     `V = {1 ≤ y ≤ T} ∪ {⌊X/a⌋}`. `V` is closed under `y ↦ ⌊y/k⌋`, since
     `⌊⌊X/a⌋/k⌋ = ⌊X/(ak)⌋`. Strong induction on `y` then gives `tables_sound`: any table that
     passes equals `M` on `V`, whatever produced it.
   - The tables come from `buildSmall` and `buildBig`, the usual `O(X^{3/4})` recursion. They are
     untrusted, and nothing about them is proved.
3. **Assembly**. [`Polya/Main.lean`](Polya/Main.lean) proves `L(906150257) = 1`, which
   contradicts `L(n) ≤ 0` at `n = 906150257`. [`Polya/Sterneck.lean`](Polya/Sterneck.lean)
   proves `M(7725038629) = 43947`. Then `√7725038629 ≤ 87894` gives
   `|M| = 43947 ≥ √x/2`, and `4·43947² = 7725355236 > x` gives the integer form.

| File | Content |
| --- | --- |
| `Polya/Statement.lean` | the fixed statements |
| `Polya/Identities.lean` | `Σ M(⌊x/n⌋) = 1`, `λ * ζ = 𝟙_□`, `L` in terms of `M` |
| `Polya/Check.lean` | block sums, table check, soundness, untrusted table builders |
| `Polya/Main.lean` | `L(906150257) = 1`, Pólya false (1 `native_decide`) |
| `Polya/Sterneck.lean` | `M(7725038629) = 43947`, von Sterneck false (1 `native_decide`) |
| `PolyaChecks/Axioms.lean` | `#guard_msgs` axiom allow-list |

## Independent recomputation

Before the Lean run, both values were computed in C with the same block algorithm and an
independent Möbius sieve for the small table. The results were `L(906150256) = 0`,
`L(906150257) = 1`, `L(906180359) = 1` (Lehman's value), `M(7725038628) = 43946` and
`M(7725038629) = 43947`. For `n = 1000` and `n = 123457` they matched a direct sieve in Python.

## Deviations from the literature

There are none in the values. We prove failure at the known points and not minimality (see
above).

## Building

```
lake build Polya PolyaChecks
```

The package uses Lean `v4.36.0` and Mathlib `fc4f59e577feb1a4956671bc04ac18aaaf8cd842`. It
needs Mathlib only, and its packages come from the repository's shared `.lake/packages`. With
Mathlib built, the whole package builds in about 2.5 minutes wall. Nearly all of that is the two
`native_decide` modules.

## Unconditional version

No unconditional version is needed. The results are tier D and do not use RH.

## Literature and prior formalisations

- G. Pólya, *Verschiedene Bemerkungen zur Zahlentheorie*, Jahresber. Deutsch. Math.-Verein. 28
  (1919), 31–40: the conjecture.
- C. B. Haselgrove, *A disproof of a conjecture of Pólya*, Mathematika 5 (1958), 141–145: a
  disproof without a witness.
- R. S. Lehman, *On Liouville's function*, Math. Comp. 14 (1960), 311–320: `L(906180359) = 1`.
- M. Tanaka, *A numerical investigation on cumulative sum of the Liouville function*, Tokyo J.
  Math. 3 (1980), 187–189: the least counterexample `906150257`.
- R. D. von Sterneck stated the conjecture `|M(x)| < ½√x` for `x > 200` in a series of papers
  with tables of `M(n)`, from 1897 to 1912. The individual papers were not read.
- W. Jurkat (1960) disproved it without a witness. G. Neubauer, *Eine empirische Untersuchung
  zur Mertensschen Funktion*, Numer. Math. 5 (1963), 1–13, found the first explicit
  counterexamples, near `7.76·10⁹`. H. Cohen and F. Dress (1979) found the least one,
  `7725038629`, with `M = 43947`.

The von Sterneck history (Jurkat, Neubauer, Cohen–Dress) was confirmed in A. M. Odlyzko and
H. J. J. te Riele, *Disproof of the Mertens conjecture*, J. reine angew. Math. 357 (1985), §1,
and in te Riele's CWI survey *The Mertens conjecture*. The Pólya references come from secondary
sources (Wikipedia, OEIS A189229, Brent–van de Lune arXiv:1112.4911) and from bibliographic
memory. The originals were not read.

**Prior Lean proofs.** We found none. We searched:

- Mathlib at the pin: its `Liouville.lean` has five lemmas, and `Counterexamples/` contains
  nothing on either conjecture.
- formal-conjectures `9097e2f`, including its `formal_proof` attributes.
- A GitHub code search for `906150257`, `7725038629`, `sterneck` and `polya conjecture` (Lean),
  which found only C, Perl, GAP and data files.
- The scout's searches. Its one Lean hit, andyprevalsky/auto-math
  `disproof-templates.lean`, states `polya_conjecture_false` with `sorry` over an `opaque`
  summatory function.

## Credits

Built with the [OpenHuman](https://github.com/tinyhumansai/openhuman) agents. Nothing is
vendored. The package uses only Mathlib (Apache-2.0). Licence: GPL v3 (`LICENSE`).
