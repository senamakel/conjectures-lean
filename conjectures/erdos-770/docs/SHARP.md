# Erdős 770(iii): a single-digit constant

Target: `h(n) ≤ max(P(n), ⌈C log² n⌉)` for every `n ≥ 2` with `C` as small as can be proved.
Written 2026-11-26 before the Lean work, numbers from the scripts listed at the end.

## 1. Where the factor 100 goes

The `200` proof (`Main200.lean`) takes a bad prime `r` (a prime dividing `iⁿ − 1` for every
`2 ≤ i ≤ M`, `M = max(P(n), K)`, `K = ⌈C log² n⌉`) and splits at `r = n¹⁰`:

* `r ≤ n¹⁰`: Bach gives `M < 2 log² r ≤ 2·10² log² n`. This is where `C = 2·10²` comes from:
  the subgroup bound is applied modulo `r`, and `r` is only known to be `≤ n¹⁰`.
* `r > n¹⁰`: `H = {x : xⁿ = 1} ⊂ (ℤ/r)ˣ` has at most `n` elements and contains every product
  of `j` distinct primes `≤ K` with `K^j < r`, so `C(π(K), j) ≤ n`. With `K^j ≈ n¹⁰` this is
  far from tight; the exponent `10` was chosen so that crude real-analysis bounds close for every
  `n ≥ 3` with no finite check.

The modulus is the bad prime `r` itself. There is no smaller modulus to use: the condition is
"`1, …, M` all lie in the subgroup `H` of `(ℤ/r)ˣ`", and `r` can be as large as `2ⁿ − 1` a priori.
The hint "least prime `p` with `p − 1 ∤ n`" does not enter: `P(n)` takes care of the primes with
`p − 1 ∣ n` (they divide every `iⁿ − 1`, `i < p`), and everything else is about bad primes `r`
with `r − 1 ∤ n`.

## 2. Optimal bookkeeping

Two changes, both inside the same argument:

1. **Replace `2 log² r` by `(log r + B(r))²`.** lls-grh proves LLS Theorem 1.1 under GRH,
   `LLS.Thm11.leastPrimeOutsideSubgroup_of_GRH : LLS.LeastPrimeOutsideSubgroup`, with standard
   axioms only: for `q ≥ 3000` and proper `H`, some prime `ℓ ∤ q` outside `H` has
   `ℓ ≤ (log q + B(q))²`. For a prime `q = r ≥ 3000`, `B(r) ≤ 6.2 − 2 log log r + 2(log log r)²/log r
   + 2 log r/(r − 1) ≤ 3.126` (maximum at `r = 3001`), so `M < (log r + 13/4)²`. For `r < 3000`
   a direct check (every prime `r < 3000`, every prime `ℓ ∣ r − 1`) shows that some `i ≤ 17` is
   not an `ℓ`-th power residue, so `M < 17` (the maximum, 17, is the least quadratic non-residue
   of `1559`). Bach's `2 log² r` is not needed at all.
2. **Split where the count actually stops working.** From `M ≥ K` we get `log r > √K − 13/4`.
   Use the count with any `K' ≤ K` and `j` with `K'^j ≤ e^{√K − 13/4}`; the right `K'` is often
   well below `K` (smaller primes allow larger `j`).

Asymptotically, with `x = √K`, `L = log K`, `j ≈ x/L`, `π(K) ≈ K/L`:
`log C(π(K), j) ≈ j log(e π(K)/j) ≈ (x/L)(L/2 + 1) = x/2 + x/L`, and the count beats `n = e^u`
once `x/2 > u = x/√C`, i.e. `C > 4`. So **this method's limit is `C = 4`** (Bach's `2` would give
`8`; the old split at `n¹⁰` gave `200`). `C = 5` has room: `√5/2 = 1.118`.

**The true shape.** `h(n) = max(3, P(n), E(n))` where `E(n)` is the least `M ≥ 3` such that no
bad prime `r` (with `r − 1 ∤ n`) divides all of `2ⁿ − 1, …, Mⁿ − 1`. The data (section 3) says
`E(n) ≤ 31` for `n ≤ 10⁵`, while `log² 10⁵ = 132`; the records `E = 5, 7, 11, 13, 17, 19, 23,
29, 31` occur at `n = 11, 35, 155, 239, 779, 2855, 5279, 9095, 15695`, and `(E − 1)/log n ≤ 3.11`
there. So the excess over `P(n)` looks closer to `O(log n)` than to `log² n`. Nothing in reach
proves that: `E(n)` is a least-non-residue problem for a subgroup modulo a prime `r ∣ 2ⁿ − 1`, and
GRH gives `log² r` for that, no better. A bound `o(log² n)` would need a new input (for instance
control of the bad primes `r` beyond the counting argument), and is not attempted.

## 3. Numerics (`n ≤ 10⁵`)

Computed with `hn.py` (fast `gcd(2ⁿ − 1, 3ⁿ − 1)`, primes `p` with `p − 1 ∣ n` stripped,
then `gcd` with `iⁿ − 1` for `i = 4, 5, …`), cross-checked against the naive definition for
`n < 700` (no mismatch). `h(n) > P(n)` for 51,121 of the 99,999 values (every odd `n` has
`P(n) = 2`).

`⌈C log² n⌉ ≥ h(n)` holds iff `C > (h(n) − 1)/log² n`. The largest values of that ratio, over the
`n ≤ 10⁵` with `h(n) > P(n)`:

| `n` | `h(n)` | `P(n)` | `(h(n) − 1)/log² n` |
|---|---|---|---|
| 3 | 3 | 2 | **1.6571** (`= 2/log² 3`) |
| 5 | 3 | 2 | 0.7721 |
| 11 | 5 | 2 | 0.6957 |
| 7 | 3 | 2 | 0.5282 |
| 35 | 7 | 2 | 0.4747 |
| 239 | 13 | 2 | 0.4001 |
| 9095 | 29 | 2 | 0.3370 |
| 15695 | 31 | 2 | 0.3214 |

So on this evidence the optimal constant valid for all `n ≥ 2` is any `C > 2/log² 3 ≈ 1.6571`,
the extremal case being `n = 3` (`h(3) = 3`, `P(3) = 2`); `C = 2/log² 3` itself fails at `n = 3`.
For `n ≥ 4` any `C > 0.7722` (extremal `n = 5`), and for `n ≥ 1000` any `C > 0.337`. (The audit's
`2.49` at `n = 3` and `1.16` for `n ≥ 5` are `h(n)/log² n`, which overstates what the ceiling
needs.) The provable `C` is therefore limited by the method (`C > 4`), not by small `n`.

## 4. What is proved

`Sharp.explicitBound5_of_lls : LLS.LeastPrimeOutsideSubgroup → ExplicitBound 5 2`, that is,
`h(n) ≤ max(P(n), ⌈5 log² n⌉)` for every `n ≥ 2`, from the single hypothesis LLS Theorem 1.1
(tier H; lls-grh proves it under GRH with standard axioms only). `#print axioms`: `[propext,
Classical.choice, Quot.sound]`. Every finite check is kernel `decide`, with no `native_decide`.

| Range | Method | Lean |
|---|---|---|
| `2 ≤ n < 216` | `gcd(2ⁿ−1, 3ⁿ−1)`, primes `p < 256` with `p − 1 ∣ n` divided out, then gcd with `iⁿ − 1` up to `i = 3` (`n < 8`) or `17` | `Finite.lean`, `finOK_all` |
| `r < 3000`, any `n ≥ 216` | every prime `r < 3000`, every prime `ℓ ∣ r − 1`: some `i ≤ 17` with `i^{(r−1)/ℓ} ≢ 1`, so `M < 17 < K` | `Primes.lean`, `smallOK_eq` |
| `216 ≤ n < 2¹¹` | 104 blocks `2^k ≤ n³² < 2^{k+1}`, `248 ≤ k ≤ 351` | `Certs32.lean` |
| `2¹¹ ≤ n < 2⁴²` | 248 blocks `2^k ≤ n⁸ < 2^{k+1}`, `88 ≤ k ≤ 335` | `Certs8.lean` |
| `2⁴² ≤ n < 2⁷⁰⁹` | 667 dyadic blocks, `K' = 2^s`, `π(2^s) ≥ ⌊2^s/s⌋` (Chebyshev) | `Certs1.lean` |
| `n ≥ 2⁷⁰⁹` | `K' = K`, `j = ⌊(√K − 13/4)/log K⌋`, Chebyshev | `Analytic.lean` |

A certificate `(K', j, m, p)` for the block `(q, k)` checks `K' ≤ Ka := ⌈5 (k a/q)²⌉`,
`K'^{jq} ≤ 2^m`, `(m b/q + 13/4)² ≤ Ka`, `C(p, j)^q ≥ 2^{k+1}` and `p ≤ π(K')`, with
`a = 0.693147 < log 2 < b = 0.6931472`. `π(K')` is an exact count (`K' ≤ 1024`) or Chebyshev at a
power of two. With `q = 8` the certificates fail just below `n = 2048`, and with `q = 32` below
`n = 216`. That sets the direct range. A direct check up to 2048 in the kernel was too slow:
`List.filter` over the primes costs about 0.2 ms per element.

**`C = 9/2` and below.** The same scheme with `C = 9/2` needs the direct check up to about
`n = 4900`. Because the asymptotic margin `√4.5/2 = 1.06` is thin, the analytic cut-over moves
to about `n = e^{77000}`, which means about `10⁵` dyadic blocks. `C = 4` has no margin left.
Going below `5` would need a sharper real-analysis tail (for example an `e^j/j^j`-type
`j!` bound and a better `π(K)` lower bound than Chebyshev's `log 2`), not more computation.

Scripts (Python, run with `-I`): `scripts/sharp_hn.py N procs` (the `h(n)` table), and
`scripts/sharp_gen.py` with `scripts/sharp_gen2.py` (the certificates, the same conditions as
`blockOK` and `piOK`).
