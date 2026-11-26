# Exceptional sets for Legendre, Oppermann, Andrica and Brocard under RH in Lean

This project proves in Lean that, under the Riemann hypothesis, each of four classical
conjectures about primes between squares fails for at most `O(log³ N)` of the first `N` indices:

* **Legendre**: for all but `O(log³ N)` of the `n ≤ N` there is a prime in `(n², (n+1)²)`;
* **Oppermann**: for all but `O(log³ N)` of the `x ≤ N` there are primes in `(x(x−1), x²)` and
  in `(x², x(x+1))`;
* **Andrica**: `√p_{n+1} − √p_n < 1` for all but `O(log³ N)` of the `n ≤ N`;
* **Brocard**: for all but `O(log³ N)` of the `n ≤ N` there are at least four primes in
  `(p_n², p_{n+1}²)`.

These are bounds for the exceptional sets, not proofs of the four conjectures, which remain open.
With the certified Lean proof of RH in
[leanprover-community/riemann-hypothesis](https://github.com/leanprover-community/riemann-hypothesis)
(Alpöge), all four bounds are proved unconditionally in Lean (`Unconditional/`). The only
analytic input is Selberg's large-gap estimate under RH (A. Selberg, *Arch. Math. Naturvid.* 47
(1943)), proved in Lean in the sibling project [erdos-233](../erdos-233/) as
`Erdos233.large_gaps_of_RH`. The Legendre bound follows D. Bazzanella, *Primes between
consecutive squares*, Arch. Math. 75 (2000) 29–34, Theorem 2, who proves the sharper
`O(f(N) log² N)` for any `f → ∞` (see Deviations). Label: **RH-consequence**. For Oppermann,
Andrica and Brocard we did not find an exceptional-set bound in the literature (searched below);
the deduction here is the same as for Legendre. Unconditionally, Bazzanella's Theorem 1 gives
`O(N^{1/4+ε})` exceptional intervals `[n², (n+1)²] ⊂ [1, N]`, that is `O(M^{1/2+ε})` exceptions
among the `n ≤ M`.

## Headline theorems

`LegendreExceptions/Statement.lean` (targets), `LegendreExceptions/Main.lean` (proofs):

```lean
-- formal-conjectures bodies, per index
def LegendreAt (n : ℕ) : Prop := ∃ p ∈ Set.Ioo (n ^ 2) ((n + 1) ^ 2), Nat.Prime p
def OppermannAt (x : ℕ) : Prop :=
    (∃ p ∈ Ioo (x * (x - 1)) (x^2), p.Prime) ∧
    (∃ p ∈ Ioo (x^2) (x * (x + 1)), p.Prime)
def AndricaAt (n : ℕ) : Prop :=
    Real.sqrt ((n+1).nth Nat.Prime) - Real.sqrt (n.nth Nat.Prime) < 1
def BrocardAt (n : ℕ) : Prop :=
    letI prev := n.nth Nat.Prime;
    letI next := (n+1).nth Nat.Prime;
    4 ≤ ((Ioo (prev^2) (next^2)).filter Nat.Prime).card

-- exceptional sets, over the index ranges of the conjectures
noncomputable def legendreExceptions (N : ℕ) : Finset ℕ := (Icc 1 N).filter (fun n => ¬ LegendreAt n)
noncomputable def oppermannExceptions (N : ℕ) : Finset ℕ := (Icc 2 N).filter (fun x => ¬ OppermannAt x)
noncomputable def andricaExceptions (N : ℕ) : Finset ℕ := (range (N + 1)).filter (fun n => ¬ AndricaAt n)
noncomputable def brocardExceptions (N : ℕ) : Finset ℕ := (Icc 1 N).filter (fun n => ¬ BrocardAt n)

def LegendreExceptionBound : Prop :=
  (fun N : ℕ => ((legendreExceptions N).card : ℝ)) =O[atTop] fun N => Real.log N ^ 3
-- OppermannExceptionBound, AndricaExceptionBound, BrocardExceptionBound: the same with the other sets

theorem LegendreExceptions.legendre_exceptions_of_RH (hRH : RiemannHypothesis) : LegendreExceptionBound
theorem LegendreExceptions.oppermann_exceptions_of_RH (hRH : RiemannHypothesis) : OppermannExceptionBound
theorem LegendreExceptions.andrica_exceptions_of_RH (hRH : RiemannHypothesis) : AndricaExceptionBound
theorem LegendreExceptions.brocard_exceptions_of_RH (hRH : RiemannHypothesis) : BrocardExceptionBound
```

`legendreConjecture_iff : LegendreConjecture ↔ ∀ n ≥ 1, LegendreAt n` (and the same for the
other three) is `Iff.rfl`, so the exceptional sets are exactly the indices at which the
formal-conjectures statements fail.

## Tier and provenance

| Theorem | Tier | Label |
|---|---|---|
| `legendre_exceptions_of_RH`, `oppermann_exceptions_of_RH`, `andrica_exceptions_of_RH`, `brocard_exceptions_of_RH` | C | RH-consequence |
| `Unconditional.legendre_exceptions`, `oppermann_exceptions`, `andrica_exceptions`, `brocard_exceptions` | U | RH-consequence |

* `RiemannHypothesis` is Mathlib's statement, as in erdos-233 and formal-conjectures.
* The four conjectures are copied word for word from
  [google-deepmind/formal-conjectures](https://github.com/google-deepmind/formal-conjectures)
  at commit `9097e2f`: `LegendreConjecture.legendre_conjecture`
  (`FormalConjectures/Wikipedia/LegendreConjecture.lean`), `Oppermann.oppermann_conjecture`
  (`Wikipedia/Oppermann.lean`), `Andrica.andrica_conjecture` (`Wikipedia/Andrica.lean`) and
  `Brocard.brocard_conjecture` (`Wikipedia/BrocardConjecture.lean`); all four are tagged
  `research open` there. formal-conjectures has no exceptional-set statement for any of them,
  so the `O(log³ N)` targets are this project's own, phrased through those definitions.
* formal-conjectures also lists `ferreira_large_n` variants (Legendre, Andrica, Brocard,
  Oppermann for all large indices), tagged `research solved` and citing L. A. Ferreira,
  [arXiv:2307.08725](https://arxiv.org/abs/2307.08725). Those entries are `sorry` there; this
  project does not use them.

## Axioms

From `lake env lean scripts/axioms.lean`:

```
'LegendreExceptions.legendre_exceptions_of_RH' depends on axioms: [propext, Classical.choice, Quot.sound]
'LegendreExceptions.oppermann_exceptions_of_RH' depends on axioms: [propext, Classical.choice, Quot.sound]
'LegendreExceptions.andrica_exceptions_of_RH' depends on axioms: [propext, Classical.choice, Quot.sound]
'LegendreExceptions.brocard_exceptions_of_RH' depends on axioms: [propext, Classical.choice, Quot.sound]
'LegendreExceptions.count_le_of_RH' depends on axioms: [propext, Classical.choice, Quot.sound]
'LegendreExceptions.nth_prime_le_cube' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Standard axioms only; no `native_decide`, no `sorry`, no `axiom` or `opaque` declarations.

## Proof outline

Write `p_k` for the `k`-th prime (`p_0 = 2`) and `d_k = p_{k+1} − p_k`.

1. **Selberg's large gaps** (erdos-233, `Erdos233.large_gaps_of_RH`): under RH there are `C`,
   `X₀` with `Σ_{X ≤ p_k < 2X, d_k ≥ h} d_k ≤ C X log² X / h` for `X ≥ X₀` and
   `256 log²(5X)/log 2 ≤ h ≤ 2X`.
2. **A prime-free interval lies in one gap** (`Core.lean`, `exists_gap`): if `(a, b)` has no
   prime and `a ≥ 2`, then `p_k ≤ a < b ≤ p_{k+1}` for some `k`.
3. **One window** (`family_card_of_RH`, `window_card_of_RH`): let `(a_i, b_i)` be pairwise
   disjoint prime-free intervals with `2X ≤ a_i < 4X` and `√a_i ≤ 2(b_i − a_i)`. Their union lies
   in the gaps of length `≥ h = √X/2` with `p_k ∈ [X, 4X)` (Bertrand gives `p_k ≥ p_{k+1}/2 > X`),
   so by step 1 at `X` and `2X`, `#{i} · (h − 1) ≤ 9 C X log² X / h`, hence `#{i} ≤ 72 C log² X`
   once `√X/2 ≥ 512 log²(10X)/log 2`.
4. **All windows** (`count_le_of_RH`): summing step 3 over `X = 2^j`, `j < log₂ B`, the
   intervals with `a_i < B` number at most `K + C' log³ B`. This sum over `log B` windows is
   where the third logarithm comes from.
5. **The `O` bound** (`isBigO_of_RH`): if the members with index `m ≤ N` have `a_m < (N+2)^8`,
   then `log B ≤ 16 log N` and their number is `O(log³ N)`.
6. **The four families** (`Main.lean`). A failure gives an interval, failures at distinct
   indices give disjoint intervals, and `√a ≤ 2(b − a)`:
   * Legendre at `n`: `(n², (n+1)²)`, length `2n + 1`.
   * Oppermann at `x`: `(x(x−1), x²)` or `(x², x(x+1))`, whichever has no prime; length `x`. The
     intervals `[x² − x, x²]`, `[x², x² + x]` tile `ℕ`, so distinct `x` give disjoint intervals.
   * Andrica at `n`: `√p_{n+1} ≥ √p_n + 1` gives `d_n ≥ 2√p_n + 1`; the interval is the gap
     `(p_n, p_{n+1})`.
   * Brocard at `n`, `p = p_n`: if each of `(p², p(p+1))`, `(p(p+1), (p+1)²)`,
     `((p+1)², (p+1)(p+2))`, `((p+1)(p+2), (p+2)²)` held a prime, these four primes would lie in
     `(p², p_{n+1}²)` because `p_{n+1} ≥ p + 2` (`brocardAt_of_four`, the argument of
     formal-conjectures' `oppermann_implies_brocard`). So one of them is prime-free; its length
     is at least `p`.
   The bound `a < (N+2)^8` uses `p_n ≤ (n+2)³` (`nth_prime_le_cube`), from Bertrand for
   `n ≤ 4` and Mathlib's Chebyshev bound `π(m) ≥ m log 2 / log m` at `m = n³` for `n ≥ 5`.

## Deviations from the literature

* **Legendre: `log³ N` against Bazzanella's `f(N) log² N`.** Bazzanella's Theorem 2 (read in the
  Politecnico di Torino post-print of the Arch. Math. paper): "Assume RH and let `f(x) → ∞`
  arbitrarily slowly. Then for every `[n², (n+1)²] ⊂ [1, N]` with `O(f(N) log² N)` exceptions we
  have the expected number of primes." His proof goes through the exceptional set for the
  asymptotic `ψ(x + h) − ψ(x) ~ h` in short intervals (Bazzanella–Perelli) and a mean-square
  bound of Saffari–Vaughan type. Ours uses only Selberg's large-gap sum, which gives
  `O(log² X)` exceptions per dyadic window; summing over the `≍ log N` windows costs the third
  logarithm. Bazzanella's statement is also stronger in kind: the expected number of primes
  `~ 2n / log n²`, not only one prime.
* **Oppermann, Andrica, Brocard.** We found no published exceptional-set bound under RH. Searched:
  formal-conjectures (`9097e2f`, the four files above and `formal_proof` attributes: only
  `bounded_gap_legendre`, a conditional statement under a gap hypothesis, has one),
  1337isnot1337/solved-conjectures, GitHub code search (`legendre_conjecture`, `Oppermann`,
  `Andrica`, `Brocard`, language Lean: no exceptional-set result; the hits are the
  formal-conjectures statements and files that assume the conjectures by `axiom` or `sorry`),
  and the web (Bazzanella 2000 and its 2004 and 2011 sequels on squares; Visser,
  *Variants on Andrica's conjecture with and without the Riemann hypothesis*, Mathematics 6
  (2018), arXiv:1804.02500, which bounds `√p_{n+1}/log p_{n+1} − √p_n/log p_n` under RH but does
  not count Andrica exceptions). The deduction is the one for Legendre with a different interval.
* **Andrica's index range** follows formal-conjectures (`n ≥ 0`); counting by `p_n ≤ X` instead
  of `n ≤ N` changes `log³ N` to `log³ X`, the same order, since `log p_N ≍ log N`.

## Layout

| File | Content |
|---|---|
| `LegendreExceptions/Statement.lean` | the four conjectures (verbatim), per-index bodies, exceptional sets, targets |
| `LegendreExceptions/Core.lean` | prime-free intervals in gaps, one window, all windows, the `O(log³ N)` lemma |
| `LegendreExceptions/Main.lean` | `p_n ≤ (n+2)³`, the four families, the four headline theorems |
| `Unconditional/LegendreExceptionsUnconditional.lean` | the four bounds with RH supplied |
| `scripts/axioms.lean`, `scripts/check-unconditional.sh` | axiom check; unconditional check |

## Building

```bash
lake build                       # target LegendreExceptions; Lean v4.36.0, Mathlib fc4f59e5
lake env lean scripts/axioms.lean
```

Requires [erdos-233](../erdos-233/) and [erdos-985](../erdos-985/) by path. Compiling this
project's three modules takes about 20 s of CPU (Core 11 s, Main 7 s, Statement 3 s) once
erdos-233 is built; erdos-233 itself has no `native_decide` and builds in about two minutes of
wall time on the build box.

## Unconditional version

| Theorem | Statement | Axioms |
|---|---|---|
| `LegendreExceptions.Unconditional.legendre_exceptions` | `LegendreExceptionBound` | not yet run |
| `LegendreExceptions.Unconditional.oppermann_exceptions` | `OppermannExceptionBound` | not yet run |
| `LegendreExceptions.Unconditional.andrica_exceptions` | `AndricaExceptionBound` | not yet run |
| `LegendreExceptions.Unconditional.brocard_exceptions` | `BrocardExceptionBound` | not yet run |

Each closes the `RiemannHypothesis` argument with `riemannHypothesis` from
leanprover-community/riemann-hypothesis, commit `507a75d91d`:

```bash
scripts/check-unconditional.sh [RH_DIR]
```

The import needs about 93 GB of cache, about 19 GB of RAM and roughly 900k open files (raise the
open-file limit first, e.g. `sudo prlimit --pid $$ --nofile=2000000:2000000`). The
riemann-hypothesis proof adds no axioms of its own. It was certified by the Lean FRO and the
Mathlib Initiative on 2026-11-21, and independent kernels accept it (math.mit.edu/~drew/grh).
This check links against the community build cache and does not repeat those kernel checks.

## Credits

Built by the OpenHuman agents. `LegendreExceptions/Statement.lean` copies statement bodies from
google-deepmind/formal-conjectures (commit `9097e2f`, Apache-2.0); see `NOTICE`. The large-gap
estimate is erdos-233's.
