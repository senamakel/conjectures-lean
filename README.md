# The least primitive root under GRH in Lean

Let `g(p)` be the least positive primitive root modulo a prime `p` and `r = ω(p − 1)` the number
of distinct prime factors of `p − 1`. Assuming the GRH, Wang Yuan (1959) proved
`g(p) = O(r⁶ (log p)²)`, and V. Shoup, *Searching for primitive roots in finite fields*,
Math. Comp. **58** (1992), 369–380, Theorem 1.3, improved this to
`g(p) = O(r⁴ (log r + 1)⁴ (log p)²)` (Wang's bound is cited from Shoup's introduction; Shoup
omits the details of the proof of Theorem 1.3, which G. Martin, Acta Arith. 80 (1997),
Corollary 3.1, rederives for the least *prime* primitive root). Unconditionally only Burgess-type
bounds `g(p) ≪ p^{1/4+ε}` are known. **Status in the literature: RH-consequence.** Nothing here
is new mathematics.

**What this repo proves is weaker than both targets**: a Lean proof that GRH implies the
exponential-in-`ω` bound `g(p) ≤ 1089 (2^{ω(p−1)} log p)²` for every odd prime `p` (the
Ankeny/Linnik route: plain character expansion of the primitive-root indicator, no sieve). Wang's
and Shoup's polynomial-in-`ω` bounds (`ShoupStatement`, `WangStatement`) are stated and **not
proved**; see [Deviations](#deviations-from-the-literature).

## Headline theorems

```lean
theorem Shoup.ankenyType_of_GRH (hGRH : DirichletLNonvanishingRightOfHalf) : AnkenyTypeStatement

theorem Shoup.leastPrimitiveRoot_le_of_GRH (hGRH : DirichletLNonvanishingRightOfHalf)
    (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) :
    HasPrimitiveRootLE p (1089 * ((2 : ℝ) ^ ω (p - 1) * Real.log p) ^ 2)

theorem Shoup.prime_primitive_root_le_of_GRH (hGRH : DirichletLNonvanishingRightOfHalf)
    (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2)
    (hlt : 1089 * ((2 : ℝ) ^ ω (p - 1) * Real.log p) ^ 2 < p) :
    HasPrimePrimitiveRootLE p (1089 * ((2 : ℝ) ^ ω (p - 1) * Real.log p) ^ 2)
```

with (from `Shoup/Statement.lean`)

```lean
def HasPrimitiveRootLE (p : ℕ) (B : ℝ) : Prop :=
  ∃ g : ℕ, 0 < g ∧ (g : ℝ) ≤ B ∧ orderOf (g : ZMod p) = p - 1

def ShoupStatement : Prop :=          -- fixed target, NOT proved
  ∃ C : ℝ, ∀ p : ℕ, p.Prime → p ≠ 2 →
    HasPrimitiveRootLE p
      (C * (ω (p - 1) : ℝ) ^ 4 * (Real.log (ω (p - 1)) + 1) ^ 4 * Real.log p ^ 2)

def WangStatement : Prop :=           -- NOT proved
  ∃ C : ℝ, ∀ p : ℕ, p.Prime → p ≠ 2 →
    HasPrimitiveRootLE p (C * (ω (p - 1) : ℝ) ^ 6 * Real.log p ^ 2)

def AnkenyTypeStatement : Prop :=     -- proved under GRH, C = 1089
  ∃ C : ℝ, ∀ p : ℕ, p.Prime → p ≠ 2 →
    HasPrimitiveRootLE p (C * ((2 : ℝ) ^ ω (p - 1) * Real.log p) ^ 2)
```

## Tier and provenance

| Theorem | Tier | Literature |
|---|---|---|
| `ankenyType_of_GRH`, `leastPrimitiveRoot_le_of_GRH`, `prime_primitive_root_le_of_GRH` | C (GRH) | RH-consequence (weaker than Wang 1959 / Shoup 1992) |
| `ankenyType_unconditional`, `leastPrimitiveRoot_le_unconditional` | U | RH-consequence |
| `ShoupStatement`, `WangStatement` | not proved | RH-consequence |

* `Erdos985.DirichletLNonvanishingRightOfHalf` is copied verbatim (in erdos-985) from
  `src/Statements.lean` of
  [leanprover-community/riemann-hypothesis](https://github.com/leanprover-community/riemann-hypothesis).
* The primitive-root predicate `orderOf (g : ZMod p) = p - 1` is the one of formal-conjectures'
  `Erdos985.erdos_985`, erdos-985 and grosswald-grh. formal-conjectures has no statement of the
  Ankeny/Wang/Shoup bounds (GitHub code search, 2026-11-24: "primitive root", "Shoup",
  "Wang Yuan", "Ankeny").
* The `O`-bounds are transcribed with an existential constant over all odd primes: for odd `p`,
  `r ≥ 1` and the right-hand sides are positive, so this is equivalent to the asymptotic form.
* What exactly Ankeny (Ann. of Math. 55 (1952)) proved about `g(p)` is reported differently in
  secondary sources (Sartori, J. Number Theory 2019: `g(p) ≪ 2^{ω} log² p`;
  Paszkiewicz–Schinzel, Math. Comp. 2002: `G(p) = O(Y² log² Y)`, `Y = 2^{ω} log p`); the
  original was not read. `AnkenyTypeStatement` is therefore named for the method, not cited as
  Ankeny's theorem.

## Axioms

`scripts/check-axioms.sh` (after `lake build`), real output:

```
'Shoup.ankenyType_of_GRH' depends on axioms: [propext, Classical.choice, Quot.sound]
'Shoup.leastPrimitiveRoot_le_of_GRH' depends on axioms: [propext, Classical.choice, Quot.sound]
'Shoup.prime_primitive_root_le_of_GRH' depends on axioms: [propext, Classical.choice, Quot.sound]
```

No `native_decide`, no finite computation, no `sorry`.

## Proof outline

All in `Shoup/Ankeny.lean`, on top of erdos-985 (which proves the analytic inputs under GRH).

1. **Indicator expansion** (`Erdos985.principal_le_of_no_prime_primitive_root`): if no prime
   `q < x ≤ p` is a primitive root, then
   `S := Σ_{n<x} Λ(n)(1 − n/x) ≤ (2^{ω(p−1)} − 1) · B`, where `B` bounds every non-principal
   weighted sum `|Σ_{n<x} Λ(n)χ(n)(1 − n/x)|`.
2. **Bach's bounds under GRH** (McGown–Treviño–Trudgian, Lemma 1; erdos-985
   `bach_nonprincipal_of_GRH`, `bach_principal_of_GRH`): `B = c(p,x) √x log p` and
   `|S − x/2| ≤ √x/20 + 3`.
3. `bachC_le_thirteen`: `c(p,x) ≤ 13` for `p ≥ 3`, `x ≥ 1`.
4. `le_of_no_prime_primitive_root_lt`: with `s = √x`, `W = 2^{ω} − 1 ≥ 1`, `L = log p ≥ 1`:
   `s²/2 ≤ 13 W L s + s/20 + 3`, so `s ≤ 33 W L` and `x ≤ 1089 (2^{ω} log p)²`.
5. Take `x = ⌊1089 (2^{ω} log p)²⌋ + 1`. If `x ≤ p`, step 4 gives a prime primitive root below
   `x`; otherwise any primitive root `g < p` (cyclicity of `(ZMod p)ˣ`) is below the bound.

## Deviations from the literature

The proved bound has `4^{ω(p−1)}` where Wang has `ω⁶` and Shoup `ω⁴(log ω + 1)⁴`. For typical
`p` both are `log^{2+o(1)} p`, but in the worst case `ω ≈ log p / log log p`, our bound is
`p^{o(1)}`-type (`exp(O(log p / log log p))`) rather than `O(log⁶ p)`.

The gap is the sieve. The full inclusion–exclusion over the prime factors of `p − 1` costs
`2^{ω}` character sums. Getting a polynomial in `ω` needs a lower-bound sieve over those primes
with polynomially many terms: Brun's sieve (Wang) or Iwaniec's shifted (linear) sieve (Shoup,
Martin). Neither is in Mathlib at the pinned revision (Mathlib has Selberg's upper-bound sieve
only), and the cheaper truncations do not reach a polynomial:

* splitting the primes at `L ≈ 2ω` (Vinogradov) and doing full inclusion–exclusion on the small
  ones gives `exp(O(ω / log ω))`;
* Brun's *pure* sieve (Bonferroni truncation at depth `k ≈ C log log ω`) gives
  `ω^{O(log log ω)}`.

See [`docs/PLAN.md`](docs/PLAN.md) for the route to `WangStatement`.

## Building

```
lake exe cache get
lake build            # target Shoup; Lean v4.36.0, Mathlib fc4f59e5
scripts/check-axioms.sh
```

Requires erdos-985 at `9538edb` (HTTPS). With erdos-985's analytic modules already built,
`Shoup.Ankeny` takes well under a minute; building erdos-985's analytic part from scratch takes
longer (its `Compute` chunks with `native_decide` are not imported here).

## Unconditional version

| Theorem | Statement | Axioms |
|---|---|---|
| `ankenyType_unconditional` | `Shoup.AnkenyTypeStatement` | see below |
| `leastPrimitiveRoot_le_unconditional` | `g(p) ≤ 1089 (2^{ω(p−1)} log p)²` for odd prime `p` | see below |

`Unconditional/ShoupUnconditional.lean` discharges the GRH hypothesis with riemann-hypothesis'
`LFunction_ne_zero_of_half_lt_re`, checked against riemann-hypothesis commit `507a75d91d`:

```
scripts/check-unconditional.sh /path/to/riemann-hypothesis
```

Real output (2026-11-24, riemann-hypothesis `507a75d91d`, community cache, not rebuilt):

```
'ankenyType_unconditional' depends on axioms: [propext, Classical.choice, Quot.sound]
'leastPrimitiveRoot_le_unconditional' depends on axioms: [propext, Classical.choice, Quot.sound]
```

The import needs about 93 GB of cache, about 19 GB of RAM and roughly 900k open files (raise the
open-file limit first, e.g. `sudo prlimit --pid $$ --nofile=2000000:2000000`).

*"The riemann-hypothesis proof adds no axioms of its own. The cache contains outputs of untrusted
builds, so this links the proofs but does not re-verify the RH/GRH proof, whose independent
verification is still pending."*

These are `AnkenyTypeStatement` and its explicit form, given the Lean proof of GRH in
leanprover-community/riemann-hypothesis, which has not been independently verified. They are not
Wang's or Shoup's theorem.

## Credits

No vendored files. The analytic inputs and the indicator expansion are erdos-985's
(`github.com/senamakel/erdos-985`, required as a lake dependency).
