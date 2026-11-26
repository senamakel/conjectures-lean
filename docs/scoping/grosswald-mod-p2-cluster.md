# Grosswald modulo `p²`: costed plan for the cluster (T1 to T5)

**Status: paused, incomplete (2026-11-26, owner's instruction).** Done: the targets quoted from
the paper, the analytic inequality, the tail threshold, the tree sizing for `ω(p−1) = 6` and for
`ω(p−1) = 10…16`, the T2 sizing, numerics for every `p < 10⁸`, and part of the novelty search.
**Not sized:** the T1/T3 tree for `ω(p−1) = 7, 8, 9`. The run was stopped after more than 10
minutes without finishing, which suggests that part grows a lot. Nothing was built and no Lean
file was edited. Scripts are in the session scratchpad and were not kept: `h.c`, `h2.c` (numerics),
`tree.c`/`tree2.c` (a C port of `grosswald-grh/scripts/treecut.c` with the extra term) and
`tail2.py`.

## 0. Targets, quoted

Kerr, McGown, Trudgian, *The least primitive root modulo p²*, arXiv:1908.11497 v1 (J. Number
Theory 215 (2020) 20–27). The arXiv text was read in full via `pdftotext`. `h(p)` is the least
primitive root mod `p²`, for **odd** `p` ("Let p be an odd prime").

- §1: "Grosswald [9] conjectured that g(p) < √p − 2 for all p > 409 and this is almost certainly
  true for h(p) as well. While we are unable to prove this, …"
- §1: "Almost certainly the statement h(p) ≤ p^{log 2/ log 3} is true for all primes, as is the
  analogue of Grosswald's conjecture: that h(p) < √p − 2 for all p > 409."
- §4: "it may be possible … to give an explicit bound on ĥ(p), the least primitive root modulo
  2p² … It seems reasonable that even ĥ(p) < p^{1/2} for all p > 1171 may be true."

This settles the "garbled `ĥ`" question in `novel-via-rh.md`. In this paper `ĥ` is the least
primitive root **mod `2p²`**, which is the least *odd* primitive root mod `p²`. It is not the
least prime one. So this is a fifth target:

| | Statement | Source |
|---|---|---|
| T1 | `h(p) < √p − 2` for every prime `p > 409` | KMT §1 |
| T2 | `h(p) ≤ p^{log 2/log 3}` for every odd prime (equality at `p = 3`) | KMT §1 |
| T3 | least **prime** primitive root mod `p²` `< √p − 2` for `p > 2791` | analogue of MTT 2016 Thm 1; not stated by KMT |
| T4 | (a) MTT: `ĝ(p) < √p − 2`, `p > 2791` (mod `p`, *published*); (b) Cohen–Trudgian Conj. 1, `g_□(p) < √p − 2`, `p > 409`; (c) OEIS A223942 (Sun 2013): "Conjecture: a(n) <= sqrt(7*p_n) for all n>0", where `a(n)` is the least prime primitive root of `p_n` (A223942 = A002233 for `n > 1`) | MTT; arXiv:1602.02440; OEIS |
| T5 | `ĥ(p)` (least primitive root mod `2p²`) `< √p` for `p > 1171` | KMT §4 ("may be true") |

## 1. The analytic inequality

**What grosswald-grh already has.** Its sieve already uses von Mangoldt weights:
`Grosswald.Sieve.principal_le_sieve` assumes no **prime** `q < x` is a primitive root.
`prime_primitive_root_of_GRH_above` gives `HasSmallPrimePrimitiveRoot p` for `p > 10¹³`, and the
tree leaves try only primes (`GrosswaldCompute.gPrimes`, primes `< 2000`). So for `p > 10¹³` the
prime version (T4a) is already proved. Only the direct range uses integer `g`
(`GrosswaldCompute.findRoot` searches `g = 2, 3, …`).

**The extra term** comes from primitive-root-sq-grh's `Indicator.key_inequality`. Take `η` of
order `p` mod `p²` (`PrimitiveRootSq.exists_eta`) and `J(n) = (1/p) Σ_{0≤j<p} η(n)^j`. Write
`σ(n) = Σ_{i∈S} ∏_{E∪{i}} fac − (s−1) ∏_E fac` for the sieve weight. Then `σ ≤ 1_prim` pointwise.
If no prime `q < x` is a primitive root mod `p²`, then every primitive prime power `n < x` lies
in `W`, so `1_prim ≤ J` on the support of `Λ`. Expanding `V` exactly as in `Sieve.lean`
(`norm_V_sub_le`, `norm_V_insert_sub_le`) gives

```
δ θ_E (S₀ − K B₁)  ≤  Σ Λ w σ  ≤  Σ Λ w J  ≤  (S₀⁺ + (p−1) B₂)/p,
K  = 2^{n−s}(2 + (s−1)/δ) − 1                      (grosswald's sieveK)
B₁ = bachC p x · √x · log p
   = (2/3)(1+2/√x+3/x^{3/2})(log p + 5/3)√x + log x + 2
B₂ = (√x + 2 + 3/x)(2/3)(2 log p + 5/3) + log x + 1.6   (PrimitiveRootSq.bach_primitive_of_GRH, N = p²)
```

at `x = ⌊√p⌋ − 2` and `w(n) = 1 − n/x`. Since `B₂ ≤ 2B₁` and `S₀⁺/p < 1 ≤ 10⁻³ B₁`, the
contradiction condition becomes grosswald's `SieveIneq` with

```
K' = K + 2.001 / (δ · θ(L₀)),
```

where `L₀` is the first `n − s` primes outside `Y`. In a tree node `θ_E ≥ θ(L₀)`, because `E`
consists of `n − s` primes outside `Y`. **`Crit.crit` is reused unchanged.** Only the rational
`K` passed to it changes: `θ(L₀)` is an exact rational, so it can be added in `Alg.bestUpper` /
`upperOk`.

**Prime versions (T3, T4, T5).** The argument above already produces a *prime* `q`: if a prime
power `q^k` is a primitive root mod `p²`, so is `q`. For T5 (an odd root), the powers of 2 also
have to be excluded. That adds `Σ_{2^k<x} log 2 ≤ log x` to the right-hand side, which is
negligible. No separate "integer" analysis is needed for any target.

**Tail.** `Tail.lean` (`2^ω < 4520 p^{1/8}`, `S = ∅`) closes at `3.42·10⁴⁶` in the float model.
With the extra term (`1/θ ≤ 6.113·(29/28)^ω`, `PrimitiveRootSq.theta_ge`) it still closes at
`3.42·10⁴⁶`; the change is invisible at 4 digits. **The tail stays at `10⁴⁷` for T1, T3 and T5.**
The Lean `sieveIneq_of_large` needs one extra step: bound `(29/28)^ω ≤ (2^ω)^{1/8}`.

**T2 with `x = ⌊p^{5/8}⌋`** (`5/8 < log 2/log 3`): `log p ≤ (8/5) log(x+1)` in place of
`2 log(x+3)`. That is a small variant of `Crit.bracket_le`. For `p ≥ 10⁴⁷`, T2 follows from T1's
tail.

## 2. Finite ranges and cost

**What the existing certificate records: nothing usable.** `segOk` and `leafOk` are `Bool`
checks. `findRoot` short-circuits on the first integer `g` that passes Lucas mod `p`, with no
mod-`p²` test, and returns no witness. So for T1, T3 and T5 the **direct range and the tree
leaves must be re-run.** One extra `Nat.powMod g (p−1) (p*p) != 1` per success, and for the prime
or odd versions `g` is restricted to `gPrimes` (minus 2 for T5). How often the least root fails
mod `p²`: below `10⁸` only at `p = 40487` (`g = ĝ = 5`; `h = 10`, least prime root mod `p²` is
13). McGown–Sorenson: below `10¹⁶`, `g ≠ h` only at 40487 and 6692367337. The heuristic
`Σ 1/p` predicts about 0.5 more in `(10⁸, 10¹³)`, and none were found. So a fallback witness is
needed in essentially no cases, and the cost is that one `powMod` per prime.

**Overhead per prime** (C count, `p < 10⁸`): an integer-`g` Lucas search costs 8.32 `powMod`s per
prime. A prime-`g` search plus the `p²` test costs 8.21, because skipping composites saves about
one test. The `p²` `powMod` is two-limb, about 2× a one-limb one, so the overhead is about +5–10%.

| Item | Status | CPU-hours |
|---|---|---|
| Direct `409 < p < 10¹³ + 10⁸`, new checker (odd prime `q`, Lucas mod `p`, `q^{p−1} ≢ 1 (mod p²)`); 2502 chunks as before | must re-run; 3.3·10⁶ CPU-s × 1.05–1.10 | **≈ 960–1010** |
| `409 < p ≤ 2791` (integer `h` for T1, T5's `1171 < p ≤ 2791`) | tiny `decide`/`native_decide` | < 0.01 |
| Tree `10¹³…10⁴⁷`, `ω = 10…14` | sized: 3.90·10¹⁰ `k` vs 1.78·10¹⁰ today (×2.2) | 61 |
| Tree, `ω = 6` | sized: 7.4·10⁷ `k` (0 today) | 0.1 |
| Tree, `ω = 15, 16` | root closes | 0 |
| Tree, `ω = 7, 8, 9` | **unsized** (2.42·10¹⁰ `k` today; the model did not finish in 10 min) | ≥ 80 if ×2.2; **risk: it may not terminate at `LOW = 10¹³`** |
| Tree total | lower estimate ≈ 9·10¹⁰ `k` × 5.6 µs | **≥ 140** |
| Node checks (interpreted, 35 ms each) | about 2× today's node count | < 5 |

Risk: if `ω ≤ 9` forces `LOW` above `10¹³`, each extra `10¹³` of direct range costs about
**920 CPU-hours**. Next step: run `tree2 10000000000001 2.001 0.5 n n` for `n = 7, 8, 9` to
completion, or with `LIM` raised, and try `LOW = 2·10¹³`.

**Per target**

- **T1, T3, T5 together**: one direct run plus one tree run, **≈ 1100–1150 CPU-hours** if
  `LOW = 10¹³` holds (about 1.2 days wall on the 95-core box, as before). The shared checker
  certifies an odd prime `q < √p − 2` for `p > 2791`, which implies all three. Below 2791, small
  checks.
- **T2 alone** (`x = ⌊p^{5/8}⌋`, its own `crit` variant, leaves reuse the T1 leaf checker since
  `√p − 2 < p^{5/8}`). Tree sizes with the extra term: `LOW = 10¹²`: 2.6·10⁵ `k`; `10¹¹`:
  6.4·10⁷; `10¹⁰`: 1.49·10⁹ (144 leaves); `10⁹`: 4.2·10⁹. Best around `LOW = 10¹⁰`: direct
  `p < 10¹⁰` ≈ 0.9 CPU-h, tree ≈ 2.3 CPU-h, so **≈ 3–4 CPU-hours** in total (about 10 direct
  chunks of `10⁹` at a few minutes each, and about 20–40 tree subtrees).
- **T4**: (a) needs only the direct range re-run with prime `g` (the tree is already prime),
  ≈ 920 CPU-h standalone, or free as a corollary of the T1/T3 run. (b) and (c) follow from (a)
  plus `p ≤ 2791` checks.

## 3. Recommendation

1. **First theorem: T2 under GRH, every odd prime** (`h(p) ≤ p^{log 2/log 3}`), ≈ 3–4 CPU-hours.
   It is a stated conjecture (KMT), unconditionally open (best `p^{2/3}`, McGown–Sorenson; their
   method's limit is `0.661`), and sharp at `p = 3`. Engineering:
   - reuse `Sieve.principal_le_sieve`'s proof (pointwise lemma changed to `σ ≤ J`), `Alg`,
     `Combi`, `Covered` and `LeafSound`, generalised;
   - reuse `PrimitiveRootSq.exists_eta`, `bach_primitive_of_GRH`, `theta_ge`, `orderOf_prime_sq`;
   - new: `principal_le_sieve_sq`, `Crit` with `log p ≤ (8/5) log(x+1)`, `KQ'` with the
     `2.001/(δθ(L₀))` term;
   - checkers `segOk`/`leafOk` with one `powMod` mod `p²` and the soundness lemmas extended
     (`numOk_sound`, `candOk_sound`).
2. **Then T1 + T3 + T5 in one run**, after the `ω = 7…9` tree is sized. If `LOW = 10¹³` holds,
   ≈ 1100–1150 CPU-hours; T4(b, c) come for free as corollaries.
3. A fallback if compute is refused: T1 for `p > 10¹³` (tree only, ≥ 140 CPU-hours), with
   `409 < p ≤ 10¹³` as a **cited hypothesis**. The range is covered by McGown–Sorenson's
   computation (`g = h` except at 2 primes), which cannot be replayed in Lean.

## 4. Numerical verification, every prime `p < 10⁸` (5,761,454 primes; C, 13 s)

- **T1**: no failure for `409 < p < 10⁸`. The tightest case is `p = 439` (`h = 15`, margin
  3.95; `h/√p = 0.716`). Largest `h` is 113 at `p = 90441961`.
- **T2**: the maximum of `log h/log p` is 0.63093 at `p = 3` (equality), then 0.56458 (`p = 7`)
  and 0.56060 (`p = 191`). It fails at `p = 2` (`h(2) = 3` mod 4), which KMT exclude by taking
  `p` odd.
- **T3**: the exceptions with `409 < p ≤ 2791` are 1021, 1031, 1811 and 2791 (the least prime
  root mod `p²` is 31, 37, 41, 53). There are none above 2791. The tightest margin above 2791 is
  20.1 at `p = 5641`. Largest witness: 223 at `p = 73189117`.
- **T4(c)** `ĝ(p) ≤ √(7p)`: no exception below `10⁸`. **T4(b)** has no exception in
  `409 < p ≤ 2791`.
- **T5** `ĥ(p) < √p`: the exceptions with `p > 13` are 23, 41, 59, 109, 131, 181, 191, 409, 421
  and **1171** (`ĥ = 35 > 34.2`), matching KMT's `p > 1171`. There are none above. The tightest
  case above 1171 is `p = 1811` (margin 1.56). The *odd prime* version fails up to `p = 2791`
  (1531, 2131 and 2791 included), so T5 needs integer witnesses on `(1171, 2791]` and primes
  above.

## 5. Novelty search (2026-11-26, partial)

Searched: Exa (3 queries: GRH bound for `h(p)`, least prime or odd primitive root mod `p²`/`2p²`,
Cohen–Trudgian and A223942 proved); formal-conjectures PRs ("primitive root", all states: #7425,
#8222 mod `p`, #7672, #7060, #3245/#2723; nothing mod `p²`); GitHub code search ("least primitive
root modulo p^2": a Python library and a citation list; `Grosswald` in Lean: formal-conjectures
985/Bateman–Grosswald, our own repos).

Found:
- KMT 2019 (the conjectures, "unable to prove");
- Chen, IJNT 2022 (`h < p^{0.74}`);
- McGown–Sorenson, Math. Comp. 2024 (`h < p^{2/3}`, `g = h` for `p ≤ 10¹⁶` except two primes,
  so **T1 holds unconditionally for `409 < p ≤ 10¹⁶` by their computation**; T1 is open above);
- Bagger 2026 (mod `p` only);
- Cohen–Oliveira e Silva–Trudgian 2016 §4 (`ĝ < √p − 2` on `(2791, 2.5·10¹⁵)`, computed);
- Hunter 2016 (`g_□ < p^{0.63093}` outside `[2.5·10¹⁵, 9.63·10⁶⁵]`).

No GRH result for T1, T2, T3 or T5 was found. T4(a) is published (MTT 2016 Thm 1), and T4(b, c)
follow from it, so they are class B.

Not yet searched: Zenodo, erdosproblems/MathOverflow, 1337isnot1337/solved-conjectures,
openai/math, and the Elliott–Murata (1998) follow-ups on `2p²`.
