# Blueprint: Erdős 770 (iii) from Bach's subgroup bound

Notation. `h n` and the target `Erdos770Part3` are formal-conjectures' (`Erdos770/Statement.lean`).
`P n = sSup {m | m.Prime ∧ m - 1 ∣ n}`; for `n ≥ 1` the set contains `2` and is bounded by
`n + 1`, so `P n` is its largest element (`P_mem`, `le_P`). `π` is `Nat.primeCounting`.
Bach's bound with constant `c = 21/5` is `Ankeny.BachSubgroupBound (21/5)` (ankeny-grh).

Headline: `explicitBound_of_bach : BachSubgroupBound (21/5) → ExplicitBound 420 2`, i.e.

    h n ≤ max (P n) ⌈420 (log n)²⌉   for every n ≥ 2,

and `erdos_770_iii_of_bach`, `erdos_770_iii_of_GRH` for part (iii). The literature
(Korsky's notes to his #769 manuscript) states `h(n) ≤ max{P(n), C (log n)²}` under GRH with an
unspecified `C`; this is that argument with Bach's bound and explicit constants.

## Steps

1. **`P n ≤ h n`** (`Basic.lean`, `P_le_h`). For `2 ≤ i < p = P n`, Fermat and `p - 1 ∣ n` give
   `p ∣ iⁿ - 1`, so no `m < p` has `gcd(2ⁿ-1, …, mⁿ-1) = 1`. (`h n = ⊤` is excluded by `le_top`;
   the `⊤` element is never in the `sInf` set, since `Icc 2 0 = ∅` has gcd `0`.)
2. **Bad prime** (`Core.lean`, `exists_bad_prime`). Let `K = ⌈420 log² n⌉ ≥ 202`,
   `M = max (P n) K`. If `gcd(2ⁿ-1, …, Mⁿ-1) ≠ 1`, a prime `r` divides every `iⁿ - 1`,
   `2 ≤ i ≤ M`; then `r > M` (else `r ∣ rⁿ - (rⁿ - 1) = 1`) and `r ≤ 2ⁿ - 1`.
   Otherwise `h n ≤ M` (`h_le_of_gcd`).
3. **Bach** (`lt_of_bach`). `H = ker (x ↦ xⁿ)` in `(ZMod r)ˣ` contains the residues `1, …, M`.
   It is proper: if `H = ⊤`, the exponent `r - 1` of the cyclic group divides `n`, so
   `r ≤ P n ≤ M`. Bach gives `a ∉ H` with `a.val ≤ (21/5) log² r`; `a.val ≤ M` would put `a` in
   `H`, so `M < (21/5) log² r`.
4. **Small `r ≤ n¹⁰`.** `(21/5) log² r ≤ (21/5)·100 log² n = 420 log² n ≤ K ≤ M`, contradicting
   step 3. (`C = (21/5)·10²`.)
5. **Large `r > n¹⁰`** (`choose_le_of_bad`). For `j` with `K^j ≤ n¹⁰`, every product of `j`
   distinct primes `≤ K` is `≤ K^j < r`, lies in `H`, and different subsets give different
   integers (`Nat.primeFactors_prod`), hence different residues. `|H| ≤ n` (`xⁿ = 1` has at
   most `n` roots in the field `ZMod r`, `Polynomial.card_nthRoots`). So `(π K).choose j ≤ n`.
6. **Numerics** (`Numerics.lean`, `numeric`, every `n ≥ 3`). With `u = log n ≥ 1`,
   `L = log K`, `j = ⌊10u / L⌋`:
   * `j L ≤ 10u`, so `K^j ≤ n¹⁰`;
   * Chebyshev in Mathlib (`psi_ge_of_seven_le`, `psi_le_primeCounting_mul_log`):
     `π(K) L ≥ K log 2 ≥ 420 u² · 0.693`, so `π(K) ≥ 29u·j ≥ (21u + 1) j`;
   * `choose ≥ (π K + 1 - j)^j / j! ≥ (21u·j)^j / j^j = (21u)^j` (`Nat.pow_le_choose`,
     `Nat.factorial_le_pow`);
   * `K ≤ 420u² + 1 ≤ (21u)²` gives `L ≤ 2 log(21u)`; with `10u < (j+1)L` this gives
     `j log(21u) > 5u - log(21u) > u`, because `log(21u) ≤ log 21 + u - 1 < 4u`
     (`log 21 < 4` from `e > 2.718`). So `(21u)^j > n`, contradicting step 5.
   `n = 2` has no large case: `r ≤ 2² - 1 < 2¹⁰`.
7. **Part (iii)** (`erdos_770_iii_of_explicit`). `log² x = o(x^ε)`
   (`isLittleO_log_rpow_rpow_atTop`), so eventually `C log² n + 1 < n^ε < P n`, the max is
   `P n`, and with step 1 `h n = P n`.

## Constants

| Constant | Value | From |
|---|---|---|
| Bach | `21/5` | ankeny-grh `bach_of_GRH` (Bach: `2`) |
| split exponent `k` | `10` (`r ≤ n¹⁰`) | chosen so step 6 holds for every `u ≥ 1` with crude bounds |
| `C` | `420 = (21/5)·k²` | step 4 |
| `n₀` | `2` | `n = 1` fails: `h 1 = 3`, `P 1 = 2`, `⌈420 log² 1⌉ = 0` |

The scoping sketch used `k = 3`, `C = 38`. Its asymptotics are right (the count is about
`n^{k/2}` and needs `k > 2`), but with `k = 3` the crude inequality of step 6 only closes for
large `n` (about `log n ≥ 10`), and the small `n` would need a finite check of `h n` that is not
feasible by `decide`. `k = 10` removes the finite range entirely. A smaller `C` is possible with
sharper bookkeeping in step 6; it was not attempted.
