# Sun's Conjecture 3.25 (OEIS A243164) under GRH in Lean

**Work in progress.** Z.-W. Sun conjectured (arXiv:1402.6641, Conjecture 3.25, 2014-06-01; Proc.
7th China–Japan Seminar, World Sci. 2015, 169–187; OEIS A243164) that for every integer
`n > 6` there is a prime `q < n` such that `q·n` is a primitive root modulo `p_n`, the `n`-th
prime. Sun checked it for `n ≤ 2·10^5`. It is open: no proof, conditional or not, was found in
the literature (search of 2026-11-26 in `docs/scoping/sun-a243164-primitive-roots.md` at the
repository root). This project proves it from GRH for Dirichlet L-functions plus one numerical
inequality, `SieveNumerics (10^8)`, which is a statement about real numbers with no
L-function in it and is not yet proved in Lean. The literature label is *RH-consequence*; the
deduction (erdos-985's argument with search length `π(p)`, twisted by `χ(n)`, with the
McGown–Treviño–Trudgian sieve) was not found published.

```lean
theorem SunA243164.sunA243164_of_GRH_of_numerics
    (hGRH : Erdos985.DirichletLNonvanishingRightOfHalf)
    (hnum : SunA243164.SieveNumerics 100000000) :
    SunA243164.SunA243164Statement                   -- SunA243164/Main.lean

def SunA243164.SunA243164Statement : Prop :=          -- SunA243164/Statement.lean
  ∀ n : ℕ, 6 < n → ∃ q : ℕ, q.Prime ∧ q < n ∧
    orderOf ((q * n : ℕ) : ZMod (Nat.nth Nat.Prime (n - 1))) = Nat.nth Nat.Prime (n - 1) - 1
```

## Tier and provenance

`sunA243164_of_GRH_of_numerics` is tier C with one further explicit hypothesis: GRH
(`DirichletLNonvanishingRightOfHalf`, copied verbatim in erdos-985 from
leanprover-community/riemann-hypothesis `src/Statements.lean`) and `SieveNumerics (10^8)`
(`SunA243164/Analytic.lean`). The project is not done until `SieveNumerics (10^8)` is proved
(`docs/PLAN.md`); then the theorem becomes `sunA243164_of_GRH` (tier C) and
`Unconditional/` gives the tier-U version. No formal-conjectures statement exists; the statement
is transcribed from Sun's paper, with `p_n = Nat.nth Nat.Prime (n - 1)`.

## Axioms

AXIOMS_PLACEHOLDER

## How the proof goes

1. **Assembly** (`Assembly.lean`). With `P = p_n` we have `π(P) = n`
   (`primeCounting_nthPrime`), so it suffices that every prime `P` of index `> 6` is a
   `GoodPrime`: some prime `q < π(P)` has `q·π(P)` primitive modulo `P`.
2. **Finite range** (`Compute/`). `verifiedBelow_10_8`: every prime `P < 10^8` of index `> 6`.
   The checker walks through `[0, 10^8)` carrying the prime count, so it knows `n = π(P)`
   exactly. For odd `m` passing the base-2 Fermat test it searches small primes `q < n` with
   `(qn)^{m−1} ≡ 1` and `(qn)^{(m−1)/r} ≢ 1` for every prime `r ∣ m − 1`: that is a Lucas
   certificate, so it proves `m` prime (Mathlib's `lucas_primality`) and `qn` primitive at once.
   `Nat.minFac` settles base-2 pseudoprimes and the primes of index `≤ 6`. Soundness:
   `Compute.countFrom_sound`. The least working `q` below `10^8` is at most 211.
3. **Twisted sieve** (`TwistedSieve.lean`). `principal_le_sieve_twisted` is MTT Theorem 3
   (grosswald-grh's `Grosswald.Sieve.principal_le_sieve`) for the indicator of `a·m` with a
   fixed unit `a`. Characters give `χ(a m) = χ(a)χ(m)`, `|χ(a)| ≤ 1`, so the GRH bound for each
   non-principal weighted sum is unchanged. Unlike in erdos-985, a prime power `q^k` with `a q^k`
   primitive does not force `a q` primitive, so the inequality carries the prime-power term
   `Epp x ≤ ψ(x) − θ(x) ≤ log 4 (√x + ⌊log₂ x⌋ x^{1/3})` (`PrimePowers.lean`, from Mathlib's
   `Chebyshev.psi_eq_theta_add_sum_theta` and `Chebyshev.theta_le_log4_mul_x`).
4. **GRH step** (`Analytic.lean`). With `x = π(P)`, `a = x mod P` and erdos-985's
   `bach_nonprincipal_of_GRH`, `bach_principal_of_GRH`, a prime that is not good violates
   `SieveIneq P S` for every admissible `S` (`not_sieveIneq_of_GRH`).
5. **Numerics** (to do). `SieveNumerics (10^8)`: for every prime `P ≥ 10^8` some `S` satisfies
   `SieveIneq P S`. Computed margins with the bounds the proof uses (Mathlib's
   `π(P) ≥ P log 2/log P`, `E` = the two smallest prime factors of `P − 1`): at least 14% in
   every case (`ω(P−1) = 8` at `P = 10^8`). Plan in `docs/PLAN.md`.

## Deviations from the literature

None in the statement. The method is MTT's (Funct. Approx. Comment. Math. 55 (2016),
arXiv:1508.05182) with search length `π(P)` instead of `√P − 2`, which is why the analysis
closes at `10^8` for every `ω(P − 1)`.

## Building

```bash
lake build SunA243164
```

Lean v4.36.0, Mathlib `fc4f59e5`; requires erdos-985 by path. The 20 `Compute.Chunk*`
modules dominate: about 96 s CPU and 6.5 GB of RAM each, about 30 CPU-minutes in all. Build at
most four at a time on a machine with less than about 130 GB of free RAM.

## Unconditional version

`Unconditional/SunA243164Unconditional.lean` discharges GRH with `LFunction_ne_zero_of_half_lt_re`
from leanprover-community/riemann-hypothesis at `507a75d91d`; `SieveNumerics (10^8)` stays an
argument until it is proved. Check with `scripts/check-unconditional.sh /path/to/riemann-hypothesis`
(not yet run). The import needs about 93 GB of cache, about 19 GB of RAM and about 900,000 open
files (`sudo prlimit --pid $$ --nofile=2000000:2000000` on Linux).

*The riemann-hypothesis proof adds no axioms of its own. The cache contains outputs of untrusted
builds, so this links the proofs but does not re-verify the RH/GRH proof, whose independent
verification is still pending.*

## How it was built

Built by OpenHuman agents.

## Credits

- `TwistedSieve.lean` adapts grosswald-grh's `Grosswald/Sieve.lean` and erdos-985's
  `Erdos985/Indicator/Lemmas.lean` (same repository).
- `powMod`, `smallPrimes` and `zmod_pow_eq_one_iff` are erdos-985's
  (`Erdos985/Compute/Checker.lean`).
- GRH statement: leanprover-community/riemann-hypothesis `src/Statements.lean`, via erdos-985.
