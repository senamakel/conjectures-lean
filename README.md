# The least primitive root under GRH in Lean

Let `g(p)` be the least positive primitive root modulo a prime `p` and `r = ω(p − 1)` the number
of distinct prime factors of `p − 1`. Assuming the GRH, Wang Yuan (1959) proved
`g(p) = O(r⁶ (log p)²)`, and V. Shoup, *Searching for primitive roots in finite fields*,
Math. Comp. **58** (1992), 369–380, Theorem 1.3, improved this to
`g(p) = O(r⁴ (log r + 1)⁴ (log p)²)` (Wang's bound is cited from Shoup's introduction; Shoup
omits the details of the proof of Theorem 1.3, which G. Martin, Acta Arith. 80 (1997),
Corollary 3.1, rederives for the least *prime* primitive root). Unconditionally only Burgess-type
bounds `g(p) ≪ p^{1/4+ε}` are known. **Status in the literature: RH-consequence.**

This repo proves in Lean, from GRH, for every odd prime `p`:

* `g(p) ≤ C · ω(p−1)^7 · (log p)²` (`PolyOmegaStatement 7`, `polyOmega7_of_GRH`), by a
  Brun–Hooley sieve over the primes dividing `p − 1` with Mertens-quality prime sums; one
  exponent above Wang's `6`;
* the earlier `g(p) ≤ C · ω(p−1)^136 · (log p)²` (`PolyOmegaStatement 136`), with the explicit
  `C = 1089 (304 · 2^21 · 16^46)²`, from the same sieve with Chebyshev-quality sums;
* `g(p) ≤ 1089 (2^{ω(p−1)} log p)²` (the Ankeny/Linnik route: plain character expansion of the
  primitive-root indicator).

With the certified Lean proof of GRH (`Unconditional/`) all three hold unconditionally. Wang's
exponent `6` (`WangStatement`) and Shoup's `ω⁴(log ω + 1)⁴` (`ShoupStatement`) are the fixed
targets in `Shoup/Statement.lean`; the gap is in [Deviations](#deviations-from-the-literature).

## Headline theorems

```lean
theorem Shoup.polyOmega7_of_GRH (hGRH : Erdos985.DirichletLNonvanishingRightOfHalf) :
    PolyOmegaStatement 7

theorem Shoup.leastPrimitiveRoot_le_seven_of_GRH
    (hGRH : Erdos985.DirichletLNonvanishingRightOfHalf) (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) :
    HasPrimitiveRootLE p (C7total * (ω (p - 1) : ℝ) ^ 7 * Real.log p ^ 2)

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

def PolyOmegaStatement (A : ℕ) : Prop := -- proved under GRH for A = 7 and 136; A = 6 is Wang
  ∃ C : ℝ, ∀ p : ℕ, p.Prime → p ≠ 2 →
    HasPrimitiveRootLE p (C * (ω (p - 1) : ℝ) ^ A * Real.log p ^ 2)
```

`polyC = 1089 * (304 * 2 ^ 21 * c16) ^ 2` with `c16 = 16 ^ 46` (both `irreducible_def`, in
`Shoup/Poly.lean`). `C7total = C7 + polyC · M0^129` (`Shoup/Poly7.lean`) is explicit but far
too large to be useful numerically: `M0 = 2^{1000·2^{23}}` is the threshold on `ω(p−1)` above
which the exponent-7 sieve runs, and `C7` contains the bottom-block constant
`(2^{2^{21}} + 1)^{2^{2^{21}+1}}`.

## Tier and provenance

| Theorem | Tier | Literature |
|---|---|---|
| `polyOmega7_of_GRH`, `leastPrimitiveRoot_le_seven_of_GRH` | C (GRH) | RH-consequence (exponent 7; Wang 1959 has 6) |
| `polyOmega_of_GRH`, `leastPrimitiveRoot_le_poly_of_GRH` | C (GRH) | RH-consequence (exponent 136) |
| `ankenyType_of_GRH`, `leastPrimitiveRoot_le_of_GRH`, `prime_primitive_root_le_of_GRH` | C (GRH) | RH-consequence (weaker than Wang 1959 / Shoup 1992) |
| `polyOmega7_unconditional`, `leastPrimitiveRoot_le_seven_unconditional`, `polyOmega_unconditional`, `leastPrimitiveRoot_le_poly_unconditional`, `ankenyType_unconditional`, `leastPrimitiveRoot_le_unconditional` | U | RH-consequence |
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
'Shoup.polyOmega7_of_GRH' depends on axioms: [propext, Classical.choice, Quot.sound]
'Shoup.leastPrimitiveRoot_le_seven_of_GRH' depends on axioms: [propext, Classical.choice, Quot.sound]
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

### Exponent 7 (`Shoup/Sieve/Mertens.lean`, `BrunHooley2.lean`, `Thresholds.lean`, `Shoup/Poly7.lean`)

Same transfer and sieve inequality as above; four inputs are sharpened.

1. **Mertens** (`Sieve/Mertens.lean`): `|Σ_{n≤N} Λ(n)/n − log N| ≤ log 4 + 4` from
   `Λ * ζ = log`, Stirling and Chebyshev's `ψ(N) ≤ (log 4 + 4) N` (all in Mathlib). Splitting
   `(2^u, 2^v]` into shells of width `w`:
   `Σ 1/ℓ ≤ log(v/u) + w(v−u)/u² + c₁((v−u)/w + 1)/u`, `c₁ = 2(log 4 + 4)/log 2 ≤ 16`.
2. **Exact Brun–Hooley identity** (`Sieve/BrunHooley2.lean`): `Φ = ∏U_j · (1 − Σ_j e_j/U_j)`,
   so the level-1 top block costs `Σ 1/ℓ` (not `Σ 1/ℓ / ∏(1 − 1/ℓ)`); Maclaurin
   `e_m ≤ (Σ y)^m/m!` and `∏(1 − y) ≥ exp(−(1+η)Σ y)` give
   `e_m/U_m ≤ σ^m/m! · e^{(1+η)σ}`. The mass is `(1 + Σ_j |B_j|) ∏_j (|B_j| + 1)^{2k_j}`
   (truncation at degree `< 2k+1` has at most `(n+1)^{2k}` terms).
3. **Blocks** (`Poly7.lean`): `m = ω(p−1)`, `n` least with `1000 m ≤ 2^{1000 n}`. Exponent
   thresholds (units of `n`) `485, 240, 138, 47, 19, 5`, then `5n/2^i` down to `[2^{20}, 2^{21})`.
   Top block `ℓ > 2^{485 n}` at level 1; five blocks at levels `3, 3, 5, 5, 7`; halving blocks at
   levels `2i + 7` (`Σ 1/ℓ ≤ 18/25` each); an exact bottom block. With
   `log(200/97) ≤ 0.7238`, …, `log(19/5) ≤ 1.3352` (Taylor, `norm_num`), the ratios sum to
   `≤ 0.9576 ≤ 24/25` for `n ≥ 2^{23}` (`ratioSumU_bsT_le`).
4. **Mass and product**: mass `≤ (1 + m) · Cbot · 2^{2385 n + 18}`; `∏_{ℓ|p−1} (1 − 1/ℓ) ≥
   2^{−n}/(9(2^{2^{20}} + 1))`. The sieve inequality gives
   `x ≤ C m² 2^{4772 n} log² p ≤ C' m^7 log² p` since `2^{1000 n} < 2^{1000} · 1000 m`.
5. Below `m = M0` the exponent-136 bound is used (`m^{136} ≤ M0^{129} m^7`).

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
| `Shoup/Sieve/Mertens.lean` | Mertens' first theorem (Λ form), prime reciprocals over shells and blocks |
| `Shoup/Sieve/BrunHooley2.lean` | exact Brun–Hooley identity, Maclaurin, sharper mass, general sieve inequality |
| `Shoup/Sieve/Thresholds.lean` | block lists from decreasing thresholds, per-block Mertens and ratio bounds |
| `Shoup/Poly7.lean` | the exponent-7 design and `polyOmega7_of_GRH` |

## Deviations from the literature

* **Exponent `7`; Wang has `6`.** In this method the bound is `x ≈ (mass · log p / δ∏(1−1/ℓ))²`,
  so the exponent is twice the exponent `M` of the mass in `m`. A Brun–Hooley sieve over blocks
  `(z^{a_{j+1}}, z^{a_j}]`, `z ≍ m`, with levels `m_j` has `M = 1 + Σ_j (m_j − 1) a_j` subject to
  `Σ_j σ_j^{m_j} e^{σ_j}/m_j! < 1`, `σ_j = log(a_j/a_{j+1})` (the `1` is the union bound over
  all `m` primes in the top block). The design here has `M = 3.384` (exponent `6.77`, rounded up to
  `7`). Optimising the continuous problem numerically (dynamic programming over levels and
  ratios) gives `M ≈ 3.28` for Brun–Hooley (exponent `≈ 6.56`) and `M ≈ 3.19` when the error
  term `e_i` of each block is multiplied by its own upper-bound sieve of lower level (`≈ 6.38`).
  Exponent `6` needs `M < 3`, i.e. a combinatorial lower-bound sieve positive at level `D = z^s`
  with `s < 3`, which no block truncation of this kind reaches. Wang–Bauer (Acta Arith. 115
  (2004), §5) quote Wang's 1959 sieve lemma (Lemma 7 there: for `r` primes the lower bound has
  error `O(r^{2.991} N)`) and conclude with `X = c m^{5.99} log² p`; Wang's own paper was not read,
  so how his lemma reaches `2.991` (presumably Brun's sieve proper, with conditions on prefixes of
  `d = q_1 q_2 ⋯`) is not reproduced here. A β-sieve (Rosser) at level `z^{2+ε}` would give
  exponent `4 + ε`, i.e. Shoup's bound up to the logarithms.
* **Constants are astronomically large.** `C7total` involves `M0 = 2^{1000·2^{23}}` and
  `(2^{2^{21}} + 1)^{2^{2^{21}+1}}`; they are explicit (`irreducible_def`) and never evaluated.
* **`ShoupStatement` needs a different sieve**: Iwaniec's linear sieve (Rosser–Iwaniec `F`, `f`).
* **Exponent 136**, the earlier result, used only Chebyshev's `θ(x) ≤ x log 4` (`Σ 1/ℓ ≤ 4` per
  block `(Y, Y²]`) and the cruder mass `(J+1)∏(|B_j|+1)^{2k_j+1}`.

## Building

```
lake exe cache get
lake build            # target Shoup; Lean v4.36.0, Mathlib fc4f59e5
scripts/check-axioms.sh
```

Requires erdos-985 at `9538edb` (HTTPS). With erdos-985's analytic modules already built, the
whole library builds in a few minutes (`Shoup.Poly` about 45 s and `Shoup.Poly7` about 2 min wall on a loaded box); building erdos-985's analytic part from scratch takes
longer (its `Compute` chunks with `native_decide` are not imported here).

## Unconditional version

| Theorem | Statement | Axioms |
|---|---|---|
| `ankenyType_unconditional` | `Shoup.AnkenyTypeStatement` | see below |
| `leastPrimitiveRoot_le_unconditional` | `g(p) ≤ 1089 (2^{ω(p−1)} log p)²` for odd prime `p` | see below |
| `polyOmega7_unconditional` | `Shoup.PolyOmegaStatement 7` | standard three |
| `leastPrimitiveRoot_le_seven_unconditional` | `g(p) ≤ C7total · ω(p−1)^7 (log p)²` for odd prime `p` | standard three |
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
'polyOmega7_unconditional' depends on axioms: [propext, Classical.choice, Quot.sound]
'leastPrimitiveRoot_le_seven_unconditional' depends on axioms: [propext, Classical.choice, Quot.sound]
```

The import needs about 93 GB of cache, about 19 GB of RAM and roughly 900k open files (raise the
open-file limit first, e.g. `sudo prlimit --pid $$ --nofile=2000000:2000000`).

*"The riemann-hypothesis proof adds no axioms of its own. It was certified by the Lean FRO and the
Mathlib Initiative on 2026-11-21, and independent kernels accept it (math.mit.edu/~drew/grh).
This check links against the community build cache and does not repeat those kernel checks."*

These prove `PolyOmegaStatement 7`, `PolyOmegaStatement 136` and `AnkenyTypeStatement`
unconditionally in Lean, with the proof of GRH (Alpöge) from riemann-hypothesis.

## Credits

No vendored files. The analytic inputs and the indicator expansion are erdos-985's
(`github.com/senamakel/erdos-985`, required as a lake dependency). The proof of Mertens' first
theorem in `Shoup/Sieve/Mertens.lean` follows the route of T. Tao et al.'s Mertens file
(mathlib4 PR #41394, Apache-2.0: `Λ * ζ = log` plus Stirling); it is written here against the
Mathlib pin, no file is copied.
