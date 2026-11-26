# Ternary Goldbach under GRH in Lean

Every odd integer `n > 5` is a sum of three primes (ternary, or weak, Goldbach). This
repository proves in Lean, with no hypothesis, that every odd `5 < n ≤ 10²⁰` is a sum of three
primes, and that ternary Goldbach follows from GRH together with Zinoviev's theorem for
`n > 10²⁰`, which enters as the named hypothesis `ZinovievTheorem`. `Unconditional/` supplies
GRH from the certified proof in
[leanprover-community/riemann-hypothesis](https://github.com/leanprover-community/riemann-hypothesis),
leaving `ZinovievTheorem` as the only hypothesis.

The repository was wound down on 2026-11-24 and is not a current target: Helfgott (2013,
arXiv:1312.7748 and arXiv:1501.05438) proved ternary Goldbach with no hypothesis.

**Literature status: known, via GRH here.** This is a Lean proof of ternary Goldbach through
GRH, given Zinoviev's theorem; ternary Goldbach is also a theorem of Helfgott (2013) by other
means. Helfgott's analytic part covers `n ≥ 10²⁷`, and Vinogradov (1937) had the statement for
all sufficiently large `n`. The GRH route followed here is Deshouillers, Effinger, te Riele and
Zinoviev (DETZ), *A complete Vinogradov 3-primes theorem under the Riemann hypothesis*,
Electron. Res. Announc. AMS 3 (1997) 99–104. In that paper, Zinoviev's circle-method theorem
(J. Number Theory 65 (1997) 334–358) covers odd `n > 10²⁰`, and a prime-gap lemma with a binary
Goldbach computation covers the rest. The finite half of DETZ is proved here completely and
without RH or GRH (label known); Zinoviev's theorem is not proved here.

```lean
theorem Goldbach.binary_goldbach_upTo : BinaryGoldbachUpTo (2 * 10 ^ 12)

theorem Goldbach.ternary_goldbach_upTo : TernaryGoldbachUpTo (10 ^ 20)

theorem Goldbach.ternary_goldbach_of_large
    (hlarge : ∀ n : ℕ, 10 ^ 20 < n → Odd n →
      ∃ p q r, Nat.Prime p ∧ Nat.Prime q ∧ Nat.Prime r ∧ n = p + q + r) :
    TernaryGoldbachStatement

theorem Goldbach.ternary_goldbach_of_GRH (hGRH : DirichletLNonvanishingRightOfHalf)
    (hZ : ZinovievTheorem) : TernaryGoldbachStatement
```

The definitions, fixed in `Goldbach/Statement.lean`:

```lean
def TernaryGoldbachStatement : Prop :=
  ∀ (n : ℕ) (_hn : 5 < n) (_hn_odd : Odd n),
    ∃ p q r, Nat.Prime p ∧ Nat.Prime q ∧ Nat.Prime r ∧ n = p + q + r

def TernaryGoldbachUpTo (N : ℕ) : Prop :=
  ∀ (n : ℕ), 5 < n → Odd n → n ≤ N →
    ∃ p q r, Nat.Prime p ∧ Nat.Prime q ∧ Nat.Prime r ∧ n = p + q + r

def BinaryGoldbachUpTo (N : ℕ) : Prop :=
  ∀ (n : ℕ), 2 < n → Even n → n ≤ N → ∃ p q, Nat.Prime p ∧ Nat.Prime q ∧ n = p + q

def ZinovievTheorem : Prop :=
  DirichletLNonvanishingRightOfHalf →
    ∀ (n : ℕ), 10 ^ 20 < n → Odd n →
      ∃ p q r, Nat.Prime p ∧ Nat.Prime q ∧ Nat.Prime r ∧ n = p + q + r
```

## Tier and provenance

| Theorem | Tier | Hypotheses |
|---|---|---|
| `Goldbach.binary_goldbach_upTo` | D | none |
| `Goldbach.ternary_goldbach_upTo` | D | none |
| `Goldbach.ternary_goldbach_of_large` | H | the range `n > 10²⁰` |
| `Goldbach.ternary_goldbach_of_GRH` | C + H | GRH and `ZinovievTheorem` |
| `ternary_goldbach_of_zinoviev` (`Unconditional/`) | U + H | `ZinovievTheorem` |

`TernaryGoldbachStatement` is the body of `TernaryGoldbachConjecture.ternaryGoldbach` in
[formal-conjectures](https://github.com/google-deepmind/formal-conjectures/blob/86a2f58a4d7a3a0637d15d5b2ce627592b54b956/FormalConjectures/Wikipedia/GoldbachConjecture.lean)
(commit `86a2f58`), copied verbatim with its binders turned into a `∀`.
`DirichletLNonvanishingRightOfHalf` is erdos-985's copy (`Erdos985/Statement.lean`) of the
statement in `src/Statements.lean` of
[leanprover-community/riemann-hypothesis](https://github.com/leanprover-community/riemann-hypothesis).
`ZinovievTheorem` is the cited hypothesis: Zinoviev (1997), as used in DETZ. It is stated in
its published form, *GRH implies* the range `n > 10²⁰`, so that the GRH hypothesis of
`ternary_goldbach_of_GRH` is the one Zinoviev's theorem consumes. GRH is used nowhere else:
the finite range needs neither RH nor GRH.

## Axioms

`lake env lean scripts/Axioms.lean` after `lake build` (2026-11-24, this commit). The full
output, 1,112 lines, is in [`docs/axioms.txt`](docs/axioms.txt). Summary:

| Theorem | Axioms |
|---|---|
| `Goldbach.binary_goldbach_upTo` | `propext`, `Classical.choice`, `Quot.sound` + 200 `native_decide` (`binary_chunk_0` to `binary_chunk_199`) |
| `Goldbach.ternary_goldbach_upTo` | the same three + 300 `native_decide` (200 binary, 100 ladder) |
| `Goldbach.ternary_goldbach_of_large` | the same three + 300 `native_decide` |
| `Goldbach.ternary_goldbach_of_GRH` | the same three + 300 `native_decide` |

The start and end of the block for `ternary_goldbach_of_GRH`, verbatim:

```
'Goldbach.ternary_goldbach_of_GRH' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Goldbach.Check.binary_chunk_0._native.native_decide.ax_1_1,
 Goldbach.Check.binary_chunk_1._native.native_decide.ax_1_1,
 Goldbach.Check.binary_chunk_10._native.native_decide.ax_1_1,
 …
 Goldbach.Check.ladder_chunk_97._native.native_decide.ax_1_1,
 Goldbach.Check.ladder_chunk_98._native.native_decide.ax_1_1,
 Goldbach.Check.ladder_chunk_99._native.native_decide.ax_1_1]
```

The repository has no `sorry` and no `axiom` or `opaque` declarations.

The `native_decide` axioms are one per chunk lemma: `Goldbach.Check.binary_chunk_j` (`j < 200`)
evaluates `goldbachChunk 9999 (6 + j·10¹⁰) 500000 10000`, the sieve check of the even numbers in
`[6 + j·10¹⁰, 6 + (j+1)·10¹⁰)`; `Goldbach.Check.ladder_chunk_j` (`j < 100`) evaluates
`ladderCover (2·10¹² − 4) lo_j hi_j`, a chain of Pocklington-certified primes across
`[lo_j, hi_j]`. On this box (shared, load about 200 during the build) a binary chunk took 490 to 770 s of wall time and a ladder chunk 160 to 280 s; on an idle core a binary chunk takes about 220 s. The checkers' soundness is proved without any such
axiom (`goldbachChunk_sound`, `ladderCover_sound`). `scripts/check-axioms.sh` prints the
axioms and fails on anything outside this allow-list.

## Proof outline

The costed plan, with the literature, the existing Lean projects and the measured rates, is in
[`docs/SCOPING.md`](docs/SCOPING.md).

1. Sieve (`Goldbach/Compute/Sieve.lean`). An odd-only segmented sieve of Eratosthenes on a
   `ByteArray`. `sieve_spec`: byte `i` is `0` exactly when some `p` in the list divides
   `x = lo + 2i` with `3p ≤ x`. `prime_of_unmarked`: an unmarked odd `x < (B+1)²` is prime if
   the list holds every odd prime `≤ B`.
2. Binary Goldbach to `2·10¹²` (`Goldbach/Compute/Binary.lean`, `BinaryAll.lean`). Each
   chunk sieves its base primes (the odd primes up to `max(9999, ⌈√H⌉)`, themselves produced by
   the sieve), then sieves segments of `10⁶` and finds, for each even `m`, an odd prime
   `p ≤ 9999` with `m − p` unmarked. `goldbachChunk_sound`.
3. Prime ladder from `2·10¹²` to `10²⁰` (`Goldbach/Compute/Ladder.lean`, `LadderAll.lean`).
   Rungs are primes `c = k·p^e + 1` with `p ≤ 31` prime and `p^{2e} > c`, certified by
   Pocklington's criterion (`prime_of_pockOK`: `a^{c−1} ≡ 1`, `gcd(a^{(c−1)/p} − 1, c) = 1`
   force every prime factor `q` of `c` to satisfy `p^e ∣ q − 1`, via Mathlib's
   `orderOf_eq_prime_pow`). Consecutive rungs are `≤ 2·10¹² − 4` apart. The search for the next
   rung is untrusted; the checker re-verifies every certificate and gap. `ladderCover_sound`.
4. Ternary Goldbach to `10²⁰` (`Goldbach/Main.lean`). For odd `n ≤ 2·10¹² + 3`,
   `n = 3 + (n − 3)`. For larger `n`, the ladder gives a prime `q ≤ n − 4` with
   `n − q < 2·10¹²`, and `n − q` is even.
5. Assembly: `ternary_goldbach_of_large` and `ternary_goldbach_of_GRH`.

## Layout

| File | Content |
|---|---|
| `Goldbach/Statement.lean` | target definitions and the cited hypothesis (fixed) |
| `GoldbachCheck.lean` | the executable checkers, core Lean only, compiled natively (`precompileModules`) |
| `Goldbach/Compute/Sieve.lean` | step 1 |
| `Goldbach/Compute/Binary.lean` | soundness of the binary checker |
| `Goldbach/Compute/Ladder.lean` | Pocklington's criterion, soundness of the ladder |
| `Goldbach/Compute/BinaryChunks/B000–B199.lean` | 200 `native_decide` chunks |
| `Goldbach/Compute/LadderChunks/L000–L099.lean` | 100 `native_decide` chunks |
| `Goldbach/Compute/BinaryAll.lean`, `LadderAll.lean` | the chunks assembled |
| `Goldbach/Main.lean` | steps 4 and 5 |
| `Unconditional/GoldbachUnconditional.lean` | GRH discharged by riemann-hypothesis |
| `scripts/gen_chunks.py` | generates the chunk files and their assemblies |
| `scripts/check-axioms.sh`, `scripts/Axioms.lean` | axiom allow-list check |
| `docs/SCOPING.md` | the costed plan |

## Deviations from the literature

Zinoviev's theorem is a hypothesis. Mathlib has no circle method, and no Lean project
formalises a GRH one. A circle method built from erdos-985's explicit formulas would
plausibly give a threshold near `10⁴³`, far above what a computation can reach (about `10²⁴`
in a day on 95 cores). See `docs/SCOPING.md`.

The finite range uses no RH. DETZ cover `10¹² ≤ n ≤ 10²⁰` with Schoenfeld's RH bound on
prime gaps (a prime within `1.615·10¹²` below every `n ≤ 10²⁰`). Here a ladder of about `5·10⁷`
certified primes does the same job unconditionally, with gap `2·10¹² − 4` and binary Goldbach
checked to `2·10¹²` (DETZ checked to `10¹³`).

## Building

Lean `v4.36.0`, Mathlib `fc4f59e5` (via erdos-985 `9538edb`).

```
lake exe cache get
lake build                 # target `Goldbach`
scripts/check-axioms.sh
```

The full build from a warm Mathlib cache took 30 min wall time and 107,000 CPU-seconds
(about 30 CPU-hours) on the shared 95-core box, almost all of it in the 300 `native_decide`
chunks, which build in parallel. The proof modules are light: `Sieve` 42 s, `Ladder` 51 s,
`Binary` 12 s, `BinaryAll` 42 s, `LadderAll` 66 s (wall, under load). The chunk parameters are in
`scripts/gen_chunks.py`; rerun it only together with a rebuild.

## Unconditional version

`Unconditional/GoldbachUnconditional.lean` imports riemann-hypothesis and discharges GRH in one
line. Zinoviev's theorem stays a hypothesis, so the result is tier U + H: ternary Goldbach
given Zinoviev's theorem, with GRH supplied by the certified proof in
leanprover-community/riemann-hypothesis. Helfgott's theorem needs neither hypothesis.

| Theorem | Statement | Axioms |
|---|---|---|
| `ternary_goldbach_of_zinoviev` | `ZinovievTheorem → TernaryGoldbachStatement` | not yet checked |

The unconditional check has not been run: the riemann-hypothesis checks are serialised across
repositories, and this repository was wound down while still in the queue. The command is:

```
scripts/check-unconditional.sh /path/to/riemann-hypothesis
```

The import needs about 93 GB of cache, about 19 GB of RAM and roughly 900,000 open files. Raise
the open-file limit first (on Linux, `sudo prlimit --pid $$ --nofile=2000000:2000000`).

The riemann-hypothesis proof adds no axioms of its own. It was certified by the Lean FRO and the Mathlib Initiative on 2026-11-21, and independent kernels accept it (math.mit.edu/~drew/grh). This check links against the community build cache and does not repeat those kernel checks.

## Credits

No file is vendored. `powModAux`/`powMod` and their correctness proof follow erdos-985's
`Erdos985/Compute/Checker.lean`. The ladder design (Proth/Pocklington rungs, untrusted search,
re-checked certificates) follows the Helfgott–Platt ladder and its Lean form in
[calr3/ternary-goldbach](https://github.com/calr3/ternary-goldbach) (Apache-2.0); no code was
copied from it.
