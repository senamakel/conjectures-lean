# The gap `2^17 ≤ q < 5·2^49`: numbers and checker design (2026-11-26)

`SharpGap` is the sharp subgroup bound for the moduli `2^17 ≤ q < 5·2^49`. This file records an
independent recount of the moduli on which lls-grh's GRH budget fails at `c = 1.657`, an exact
check of the sharp bound on every one of them, and the design of the two checkers that close the
gap in Lean.

## Phase A: the failing moduli

### The budget, as the Lean definitions state it

For a block `[a, b)` of moduli, `x = ⌊c La²⌋` with `La ≤ log a`, and a modulus `q` in the block
passes when (`LLS.budgetQ_nonpos`, `BachSharp.GoodC`)

    base2(x, Pc) − κ(x) log b − Σ_{p | q, p ≤ x} W_p(x) > 0,

with `base2`, `Kc`, `kap`, `Eshift`, `Etil` from `LLS/Bach2/Budget.lean`, `LLS/Numerics/Budget.lean`
and `LLS/Defs.lean`, `Pc` the exact Cesàro sum `Σ_{n≤x} Λ(n)/n (1 − n/x)` for `x < 2000`, and
`W_p = A_p + max(0, A_p − κ log p)`, `A_p = (log x − ½ log p)²/2 + 2K log p/(p − 1)`. The cost
depends on `q` only through its *kernel*, the set of primes `p ≤ x` dividing `q`, and only
through the sum of positive weights `W_p`, so failing is closed under adding primes.

`scripts/gap/fail.c` (float, written from these definitions, not from the earlier sizing
script) walks the blocks `[a, a + ⌊a/2^10⌋)` from `2^17` to `5·2^49`, enumerates by depth-first
search the squarefree products `P < b` of primes `≤ x` whose weight reaches the budget (pruned
by `weight + max_{p' ≥ p}(W_{p'}/log p') · log((b−1)/P) < budget`), and lists the multiples of
each minimal such `P` in the block, each modulus once (canonical leaf). 24,378 blocks, 2.1 s.

| | this recount | earlier estimate (`docs/PLAN.md`) |
|---|---|---|
| failing moduli in `[2^17, 5·2^49)`, block budget | **1,018,780** | about 1.25·10^6 (density estimate) |
| the same with each `q`'s own `x = ⌊c log² q⌋` and `log q` (`exactq.c`) | 1,015,321 | |
| `Σ q` over them | 5.16·10^15 | 6.2·10^15 |
| largest failing modulus | **9,814,524,629,910 ≈ 2^43.16** `= 2·3·5·7·11·13·17·19·23·29·37·41` | "near 2^43.4" |
| largest prime factor of any failing modulus | 44,587 (`q = 9,363,270`) | |
| blocks above `2^50` (where `x ≥ 2000` without a cap) | none fail with `x` capped at 1999 | |

So the failing set is about 1.02·10^6 moduli, all `44587`-smooth, none above `2^43.2`. Capping
`x` at `1999` changes nothing (the exact Cesàro sum at `x < 2000` beats `log x − 2`).

### The sharp bound on every failing modulus (exhaustive)

`scripts/gap/gen.c` computes `g(q)`, the least prime `y` such that the primes `≤ y` not dividing
`q` generate `(ℤ/q)ˣ`, by the Frattini rank test (for every prime `ℓ | φ(q)`, the images in
`G/G^ℓ` span; coordinates `a ↦ a^{φ(p^e)/ℓ} mod p^e` on each odd component, `a mod 4` and
`a mod 8` on `2^e`; discrete logarithms in the order-`ℓ` subgroups by brute force). It agrees
with breadth-first search (`bfs.py`) for every `3 ≤ q < 1500`.

On **all 1,018,780 failing moduli** (4.1 s): `g(q) ≤ (2/log² 3) log² q` holds for every one.
**No counterexample.** The largest ratio `g(q)/log² q` is `0.4923` (`q = 164220`, `g = 71`), and
`g(q) ≤ 113` throughout. The moduli that pass the budget satisfy the bound under GRH by lls-grh's
analytic theorem, so the statement has no counterexample in the gap if GRH holds.

## The two checkers

### 1. Kernel enumeration per block (`BachSharpGapCheck.blockOKG`)

Same block data as lls-grh's checker with constant `1657/1000` (`mkBDC`: `x`, rational bounds,
the integer budget `Bn ≤ SC·Bq` and integer weights `Wn_p ≥ SC·W_p`, `SC = 2^32`). If the
uniform budget passes, the block is done. Otherwise a depth-first search over the list
`(p, Wn_p, ρ_p)` of primes `p ≤ x` (ascending, `ρ` a suffix maximum of `⌈Wn_p / λ(p)⌉`,
`λ(n) = ⌊log₂ n^8⌋`), with state `(rest, P, w, excl)`:

* prune when `w < Bn` and either `rest = []`, its head exceeds `R = ⌊(b−1)/P⌋`, or
  `w + ρ_head · (8 log₂ R + 8) < Bn` (`λ` is superadditive, the primes of `rest` dividing `q/P`
  have product `≤ R`);
* when `w ≥ Bn` or `P` has at most `T` multiples in `[a, b)`, run through the multiples `q` of
  `P` in the block: skip `q` divisible by an excluded prime (another leaf owns it), accept it if
  `w + Σ_{p ∈ rest, p | q} Wn_p < Bn`, else require the generation certificate;
* otherwise branch on the head `p`: include (`P·p`, `w + Wn_p`; needs `p ∤ P`) and exclude
  (`p` added to `excl`).

Soundness (`dfs_sound`): if the search returns `true` then for every `q` with `a ≤ q < b`,
`P | q` and no prime of `excl` dividing `q` unless it divides `P`, either
`w + Σ_{p ∈ rest, p | q} Wn_p < Bn` or the certificate holds at `q`. At the root this is
"`sumDiv q wl 0 < Bn` or the certificate", which feeds `bach_of_goodC` exactly as lls-grh's
per-modulus branch does. The monotonicity in `log q` enters through the block: `x` is taken at
`La ≤ log a ≤ log q` and the `κ log q` term at `Lb ≥ log b > log q`, with `x ≤ c log² q` and
`κ ≥ 0`, so a pass at the block bounds passes at every `q` in it (`blockOKC_sound`, reused).

Prototype (`scripts/gap/dfs.c`, the same integer arithmetic): `T = 4`, 33.6·10^6 search nodes,
4.1·10^8 inner operations, 0.43 s; it finds exactly the 1,018,780 failing moduli, none twice.

### 2. Generation certificate per failing modulus (`BachSharpGapCheck.genCert q x`)

1. Factor `q = ∏ p_j^{e_j}` by trial division; check the product, `p_j` prime, `p_j` strictly
   increasing. Components `Q_j = p_j^{e_j}`, `n_j = p_j^{e_j−1}(p_j − 1) = φ(Q_j)`.
2. Factor every `n_j` by trial division into primes; `L` the union of these primes.
3. For each `ℓ ∈ L`: coordinates `ψ_i : (ℤ/q)ˣ → (ℤ/N_i)ˣ`, `ψ_i(u) = (u mod N_i)^{E_i}`, one
   `(Q_j, n_j/ℓ)` per odd component with `ℓ | n_j`, and for `ℓ = 2` also `(4, 1)` if `4 | q` and
   `(8, 1)` if `8 | q`. Each `ψ_i` kills `ℓ`-th powers. With the primes `s ≤ x`, `s ∤ q` as
   candidates, build by elimination over `𝔽_ℓ` words `h_i = ∏ s^{e_s}` (exponents `< ℓ`) in
   echelon form: `ψ_k(h_i) = 1` for `k < i`, `ψ_i(h_i) ≠ 1`. Only this check is trusted: the
   verifier recomputes each `h_i mod q` from its word and the `ψ_k(h_i)`.

Soundness (`closure_eq_top_of_genCert`), from three lemmas:

* **Frattini.** In a finite commutative group, if `H ⊔ G^ℓ = ⊤` for every prime `ℓ` then
  `H = ⊤` (otherwise `G/H ≠ 1` has a prime `ℓ | |G/H|`, its `ℓ`-th power map is not injective by
  Cauchy, hence not onto).
* **Echelon count.** If `ψ_1, …, ψ_r` kill `G^ℓ` and `h_1, …, h_r ∈ H` are in echelon form, then
  `(c, y) ↦ ∏ h_i^{c_i} · y` is injective on `[0, ℓ)^r × G^ℓ`, so `|H ⊔ G^ℓ| ≥ ℓ^r |G^ℓ|`; and
  `|G^ℓ| · |G[ℓ]| = |G|`. So `|G[ℓ]| ≤ ℓ^r` gives `H ⊔ G^ℓ = ⊤`.
* **Torsion count.** `|(ℤ/q)ˣ[ℓ]| ≤ ∏_j |(ℤ/Q_j)ˣ[ℓ]|` (CRT injectivity), and
  `|(ℤ/p^e)ˣ[ℓ]| ≤ ℓ` if `ℓ | n` else `1` for odd `p` (cyclic, Mathlib
  `isCyclic_units_of_prime_pow`); for `2^e`: `1` if `ℓ` odd, and `1, 2, 4` for `e = 1, 2, ≥ 3`
  (`(ℤ/2^e)ˣ = ⟨5⟩ × ⟨−1⟩`, Mathlib `isComplement'_zpowers_unitFive_neg_one`). This is exactly
  `ℓ^r` for the coordinate list above.

Prototype (`gen.c`, the same test computing all of `g(q)`): 4.1 s for all failing moduli.

### Cost estimate

Compiled Lean with `Nat` arithmetic is 20 to 100 times slower than this C: estimated 1 to 15
minutes for the search and 2 to 10 minutes for the certificates, split into chunks by range of
`q`. Well under the 10 CPU-hour stop line.
