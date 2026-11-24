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

**What this repo proves is weaker than both targets.** Two Lean proofs from GRH, for every odd
prime `p`:

* a polynomial-in-`ω` bound `g(p) ≤ C · ω(p−1)^136 · (log p)²` (`PolyOmegaStatement 136`), with
  an explicit but astronomically large `C = 1089 (304 · 2^21 · 16^46)²`, from a Brun–Hooley sieve
  over the primes dividing `p − 1` built in this repo;
* the exponential-in-`ω` bound `g(p) ≤ 1089 (2^{ω(p−1)} log p)²` (the Ankeny/Linnik route: plain
  character expansion of the primitive-root indicator).

Wang's exponent `6` (`WangStatement`) and Shoup's `ω⁴(log ω + 1)⁴` (`ShoupStatement`) are
stated and **not proved**; see [Deviations](#deviations-from-the-literature). Like Wang's and
Shoup's, the polynomial bound is `(log p)^{O(1)}` for every `p` (here `(log p)^{138}` in the worst
case), so it already shows that GRH gives a primitive root below a fixed power of `log p`.

## Headline theorems

```lean
theorem Shoup.polyOmega_of_GRH (hGRH : DirichletLNonvanishingRightOfHalf) :
    PolyOmegaStatement 136

theorem Shoup.leastPrimitiveRoot_le_poly_of_GRH (hGRH : DirichletLNonvanishingRightOfHalf)
    (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) :
    HasPrimitiveRootLE p (polyC * (ω (p - 1) : ℝ) ^ 136 * Real.log p ^ 2)

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

def PolyOmegaStatement (A : ℕ) : Prop := -- proved under GRH for A = 136; A = 6 is Wang
  ∃ C : ℝ, ∀ p : ℕ, p.Prime → p ≠ 2 →
    HasPrimitiveRootLE p (C * (ω (p - 1) : ℝ) ^ A * Real.log p ^ 2)
```

`polyC = 1089 * (304 * 2 ^ 21 * c16) ^ 2` with `c16 = 16 ^ 46` (both `irreducible_def`, in
`Shoup/Poly.lean`).

## Tier and provenance

| Theorem | Tier | Literature |
|---|---|---|
| `polyOmega_of_GRH`, `leastPrimitiveRoot_le_poly_of_GRH` | C (GRH) | RH-consequence (weaker than Wang 1959 / Shoup 1992) |
| `ankenyType_of_GRH`, `leastPrimitiveRoot_le_of_GRH`, `prime_primitive_root_le_of_GRH` | C (GRH) | RH-consequence (weaker than Wang 1959 / Shoup 1992) |
| `polyOmega_unconditional`, `leastPrimitiveRoot_le_poly_unconditional`, `ankenyType_unconditional`, `leastPrimitiveRoot_le_unconditional` | U | RH-consequence |
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
'Shoup.polyOmega_of_GRH' depends on axioms: [propext, Classical.choice, Quot.sound]
'Shoup.leastPrimitiveRoot_le_poly_of_GRH' depends on axioms: [propext, Classical.choice, Quot.sound]
```

No `native_decide`, no finite computation, no `sorry`.

## Proof outline

### Polynomial bound (`Shoup/Sieve/`, `Shoup/Poly.lean`)

Fix a character `ψ` of order `p − 1`. For a prime `ℓ ∣ p − 1` let `y_ℓ(n) ∈ {0,1}` record
whether `n` is an `ℓ`-th power residue, and `w(n) = Λ(n)(1 − n/x)`.

1. **Bonferroni** (`Sieve/Bonferroni.lean`): truncated inclusion–exclusion
   `G m B y = Σ_{T⊆B, |T|<m} (−1)^{|T|} ∏_T y` is an upper bound for `∏_B (1 − y)` for odd `m`
   and a lower bound for even `m` (`0 ≤ y ≤ 1`); the error term `E m B y` (elementary symmetric)
   satisfies `E/∏(1 − y) ≤ τ^{-m} exp((τ+2) Σ_B y)` (`E_div_prod_le`).
2. **Brun–Hooley** (`Sieve/BrunHooley.lean`): blocks `B_j` with levels `2k_j+1`;
   `Φ = ∏ U_j − Σ_i e_i ∏_{j≠i} U_j` satisfies `Φ(y) ≤ ∏_j ∏_{B_j}(1 − y)` pointwise and
   `Φ(1/ℓ) ≥ ∏(1 − 1/ℓ)·(1 − Σ_j e_j/A_j)`; it is a combination of squarefree monomials of mass
   `≤ (J+1) ∏_j (|B_j|+1)^{2k_j+1}` (`Sieve/Rep.lean`).
3. **Transfer** (`Sieve/Transfer.lean`): for `U ⊆ primeFactors(p−1)` with product `d`,
   `|Σ_{n<x} w(n) ∏_U y_ℓ(n) − S(x)/d| ≤ B`, `B` a bound for every non-principal
   `Σ w(n)χ(n)` (via erdos-985's `norm_W_le`); hence `|Σ w Φ(y(n)) − S Φ(1/ℓ)| ≤ mass · B`.
4. **Sieve inequality** (`Sieve/Main.lean`): if no `0 < g < x ≤ p` is a primitive root then
   `Σ w Φ(y(n)) ≤ 0`; with `B = 13 √x log p` and `S ≥ x/2 − √x/20 − 3` (erdos-985's GRH bounds),
   `x ≤ 1089 (2 (J+1) mass log p / ∏(1 − 1/ℓ))²`.
5. **Blocks** (`Poly.lean`): `r = ω(p−1)`, `t` least with `16 r ≤ 2^{2^t}`. Top block
   `ℓ > 2^{2^t}` at level 1 (`Σ 1/ℓ ≤ 1/16`); bottom block `ℓ = 2` (exact); middle blocks
   `(2^{2^i}, 2^{2^{i+1}}]`, `i < t`, at level `2(t−1−i)+19`, with `Σ 1/ℓ ≤ 4` from Chebyshev's
   `θ(x) ≤ x log 4` over dyadic shells (`Sieve/Primes.lean`). Ratio sum `≤ 1/15 + 0 + 1/5`
   (`τ = 5`, `e^{28}/5^{19} ≤ 1/10`). Mass `≤ 8 (r+1)^{21} (16 r)^{46}` (the lower blocks have
   `≤ 2^{2^{i+1}}` elements and `Σ_{i<T} 2^{i+1}(2(T−i)+19) ≤ 46·2^T`), `J + 1 ≤ 19 r`,
   `∏(1 − 1/ℓ) ≥ 1/(r+1)`. Altogether `x ≤ polyC · r^{136} (log p)²`.
6. Take `x = ⌊polyC r^{136} log² p⌋ + 1`; if `x > p`, any primitive root `< p` is below the bound.

### Exponential bound (`Shoup/Ankeny.lean`)

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

## Layout

| File | Content |
|---|---|
| `Shoup/Statement.lean` | targets: `ShoupStatement`, `WangStatement`, `AnkenyTypeStatement`, `PolyOmegaStatement` |
| `Shoup/Ankeny.lean` | exponential bound, `exists_primitiveRoot_lt` |
| `Shoup/Sieve/Bonferroni.lean` | truncated inclusion–exclusion, error-term bounds |
| `Shoup/Sieve/Rep.lean` | squarefree monomial expansions and their mass |
| `Shoup/Sieve/BrunHooley.lean` | the Brun–Hooley sieve function, pointwise and main-term bounds |
| `Shoup/Sieve/Transfer.lean` | power-residue indicators to character sums |
| `Shoup/Sieve/Main.lean` | the sieve inequality under GRH |
| `Shoup/Sieve/Primes.lean` | Chebyshev-based prime reciprocal sums, `∏(1 − 1/ℓ) ≥ 1/(r+1)` |
| `Shoup/Poly.lean` | the block decomposition and `polyOmega_of_GRH` |

## Deviations from the literature

* **Exponent `136` instead of Wang's `6`.** The sieve is Brun's in Hooley's formulation with crude
  parameters: the only prime-distribution input is Chebyshev's `θ(x) ≤ x log 4`, which bounds
  `Σ 1/ℓ` over a block `(Y, Y²]` by `4` (the truth is `log 2 + o(1)`). That forces truncation
  levels `≥ 19` for the block that may contain `r` primes and growing levels below it, and the
  cost (number of character sums) is `≈ r^{68}`; the bound is its square. The doubly exponential
  thresholds `2^{2^i}` also double the cost of the second block (`16 r` instead of `√(16r)`
  elements).
* **The constant is astronomically large** (`≈ 3·10^{131}`); it is explicit but not meant to be
  used numerically.
* **`ShoupStatement` needs a different sieve.** Shoup's `T ≥ c₁A/(log r + 1)² − c₂ r² B` is
  Iwaniec's shifted (linear) sieve, whose lower bound needs the Rosser–Iwaniec theory
  (`F`, `f` functions); no combinatorial truncation of the kind used here gets cost `r²`.
* Reaching **`WangStatement` (`A = 6`)** with this method would need cost `≈ r³`. Sharper
  inputs bring the exponent down (Mertens-quality `Σ 1/ℓ ≈ log 2` per block gives levels
  `≈ 5`–`7`, `A` in the 30s–40s), but `6` would need Wang's own combinatorics; see
  [`docs/PLAN.md`](docs/PLAN.md).

## Building

```
lake exe cache get
lake build            # target Shoup; Lean v4.36.0, Mathlib fc4f59e5
scripts/check-axioms.sh
```

Requires erdos-985 at `9538edb` (HTTPS). With erdos-985's analytic modules already built, the
whole library builds in about a minute of CPU (`Shoup.Poly` about 45 s wall on a loaded box); building erdos-985's analytic part from scratch takes
longer (its `Compute` chunks with `native_decide` are not imported here).

## Unconditional version

| Theorem | Statement | Axioms |
|---|---|---|
| `ankenyType_unconditional` | `Shoup.AnkenyTypeStatement` | see below |
| `leastPrimitiveRoot_le_unconditional` | `g(p) ≤ 1089 (2^{ω(p−1)} log p)²` for odd prime `p` | see below |
| `polyOmega_unconditional` | `Shoup.PolyOmegaStatement 136` | standard three |
| `leastPrimitiveRoot_le_poly_unconditional` | `g(p) ≤ polyC · ω(p−1)^136 (log p)²` for odd prime `p` | standard three |

`Unconditional/ShoupUnconditional.lean` discharges the GRH hypothesis with riemann-hypothesis'
`LFunction_ne_zero_of_half_lt_re`, checked against riemann-hypothesis commit `507a75d91d`:

```
scripts/check-unconditional.sh /path/to/riemann-hypothesis
```

Real output (2026-11-24, riemann-hypothesis `507a75d91d`, community cache, not rebuilt):

```
'ankenyType_unconditional' depends on axioms: [propext, Classical.choice, Quot.sound]
'leastPrimitiveRoot_le_unconditional' depends on axioms: [propext, Classical.choice, Quot.sound]
'polyOmega_unconditional' depends on axioms: [propext, Classical.choice, Quot.sound]
'leastPrimitiveRoot_le_poly_unconditional' depends on axioms: [propext, Classical.choice, Quot.sound]
```

The import needs about 93 GB of cache, about 19 GB of RAM and roughly 900k open files (raise the
open-file limit first, e.g. `sudo prlimit --pid $$ --nofile=2000000:2000000`).

*"The riemann-hypothesis proof adds no axioms of its own. The cache contains outputs of untrusted
builds, so this links the proofs but does not re-verify the RH/GRH proof, whose independent
verification is still pending."*

These are `PolyOmegaStatement 136`, `AnkenyTypeStatement` and their explicit forms, given the Lean proof of GRH in
leanprover-community/riemann-hypothesis, which has not been independently verified. They are not
Wang's or Shoup's theorem.

## Credits

No vendored files. The analytic inputs and the indicator expansion are erdos-985's
(`github.com/senamakel/erdos-985`, required as a lake dependency).
