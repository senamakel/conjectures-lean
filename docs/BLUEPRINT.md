# Blueprint

Source: Lamzouri, Li, Soundararajan, *Conditional bounds for the least quadratic non-residue
and related problems*, Math. Comp. 84 (2015), arXiv:1309.3595 (corrected v3 source,
`QuaResL1Corrected.tex`). Every step below is a Lean statement with its constant. All of them
are proved. Notation: `χ` is primitive and non-trivial mod `N`; `Λ(s, χ)` is Mathlib's
`completedLFunction` (no conductor factor); `D(s) = Λ'/Λ(s)`; `Z2 = Σ_ρ m_ρ/|ρ|²`
(`= 2|Re B(χ)|` in LLS).

## Assembly (top down)

1. `LLS.leastNonresidueBelowLogSq_of_GRH : GRH → LeastNonresidueBelowLogSq` (LLS Cor. 1.2):
   `q < 2^12` by kernel-checked certificates (`LLS/NonresidueCert.lean`), `q ≥ 2^12` by
   `LLS.nonresidue_large`.
2. `LLS.bach_of_GRH : GRH → Ankeny.BachSubgroupBound (11/4)`: `q < 2^18` by
   `LLS.bach_small114` (ankeny-grh's checker, 16 `native_decide` chunks), `q ≥ 2^18` by
   `LLS.bach_large114`. Corollaries: `LeastNonresidueBound (11/4)`, `Miller.MillerStatement (11/4)`.
3. `LLS.bach_of_goodQ`: `GoodQ c q` (some `64 ≤ x ≤ c log² q` with `Φ(x, log q) > 0`,
   `β ≤ κ`) gives the subgroup bound at `q`. Same for primes with `GoodP`/`Φ₁`.
4. `GoodQ (11/4) q` for `2^18 ≤ q < 2^700`: 28 certified intervals
   (`Numerics/Intervals114.lean`); `q ≥ 2^700`: `LLS.goodQ_tail114`. `GoodP 1 q` for `2^12 ≤ q < 2^700`: 153 intervals
   (`Numerics/IntervalsP.lean`); `q ≥ 2^700`: `LLS.goodP_tail`.
5. `LLS.Phi_nonpos`: if `χ ≠ 1` mod `q` is `1` on every `n ≤ x` prime to `q`, `x ≥ 64` and
   `β(x) ≤ κ(x)`, then `Φ(x, log q) ≤ 0`, where with `s = √x`, `l = log x`,
   `K = (s + 1 + l/2)/(1 + 1/x − 2/s)`, `κ = K(1 − 1/x) + l/2`, `β = l²/(2 log 17) + K/8`:
   `Φ = x − (3/20)s − 3l − 3 + 2K(l − 2) − κL − 2K E(x) + ½ log π · l − Ẽ(x) − βL
        − Σ_{p<17} max(0, W_p − β log p)`.
   `LLS.Phi1_nonpos` is the version for prime `q > x`, with no loss terms (`Φ₁`).
6. `LLS.key` (LLS §3): with `ψ` the primitive character inducing `χ`, conductor `f`,
   `l_f = log f`, `R = {p ∣ q : p ∤ f}`:
   * `Z (1 + 1/x − 2/√x) ≤ l_f (1 − 1/x) − 2(log x − 2 − Lc_q − Lc_R) + 2E(x)`,
   * `x − (3/20)√x − 3 log x − 3 − Ll_q − Ll_R ≤ (√x + 1)Z + ((l_f + Z)/2) log x
       − ½ log π log x + Ẽ(x)`,
   * `l_f + Σ_{p∈R} log p ≤ log q`.
   Obtained by symmetrising over `ψ` and `ψ⁻¹` (`Z2 ψ = Z2 ψ⁻¹ = log f + Re D(1,ψ) + Re D(1,ψ⁻¹)`).
7. Losses (`LLS/Losses.lean`, `Numerics/Budget.lean`): `Σ_{n≤x} Λ(n)w(n) Re φ(n) ≥ Σ Λ w −
   Σ_{p∣q} Σ_{p^k≤x} Λ w − Σ_{p∈R} Σ_{p^k≤x} Λ w`;
   `Σ_{p^k≤x} log p log(x/p^k) ≤ (log x − ½ log p)²/2`, `Σ_{p^k≤x} Λ/p^k (1 − p^k/x) ≤
   log p/(p − 1)` (LLS Lemma 3.1, sharpened).

## Analytic inputs (each proved, standard axioms only)

| Lean | LLS | Statement |
|---|---|---|
| `LLS.re_logSum_le` | Lemma 2.2 | `Re Σ_{n≤x} Λχ(n) log(x/n) ≤ (√x+1) Z2 + (log N + Re D(1,χ⁻¹)) log x − ½ log π log x + π²/6 − (γ/2) log x` |
| `LLS.re_cesShift_le` | Lemma 2.3 | `Re Σ_{n<x} Λχ(n)/n (1−n/x) ≤ −Re D(1,χ) − (log N + Re D(1,χ⁻¹))/x + Z2/√x + E(x)`, `E(x) = −½(1−1/x) log π − (γ/2)(1−1/x) + (log x+2)/x` |
| `LLS.Z2_eq` | (2.4) | `Z2 = log N + Re D(1,χ) + Re D(1,χ⁻¹)` |
| `LLS.psiLog_ge` | Lemma 2.1 (weaker) | `Σ_{n≤x} Λ(n) log(x/n) ≥ x − (3/20)√x − 3 log x − 3` (Abel summation from erdos-985's principal bound) |
| `LLS.vonMangoldt_ces_ge` | Lemma 2.4 (weaker, unconditional) | `Σ_{n<x} Λ(n)/n (1−n/x) ≥ log x − 2` |

`re_logSum_le` needs a new Perron kernel `x^s/s²` (`Analytic/Log/Perron.lean`: Mellin
transforms of `log t` and `log² t` on `(0,1]`, the weighted Perron formula, the residues of
`x^s/((s−w)s²)` and `x^s/s³`), an exact identity
`S = −Σ_ρ m_ρ (x^ρ − 1)/ρ² − D(0) log x + Γ̃(x)` (`Log/Identity.lean`) and the gamma part via the
digamma series (`Log/Gamma.lean`). `re_cesShift_le` reuses erdos-985's Cesàro kernel with the
coefficients `χ(n)Λ(n)/n` and zeros shifted to `ρ − 1` (`Analytic/Shift/`).

## Numerics

Each certified interval `[Q_a, Q_b)` fixes `x ≤ c (log Q_a)²`; bounds
`2^k ≤ m^64 ≤ 2^{k'}` for `log Q_a`, `log Q_b`, `log x` (`decide +kernel`), rational bounds for
`√x`, and a rational inequality `PhiLo > 0` (`norm_num`). `LLS.Phi_ge_PhiLo` proves
`PhiLo ≤ Φ` by monotonicity. Interval data comes from `scripts/emitfile.py` (`c = 11/4`) and
`scripts/emit1.py` (`c = 1`, primes).

Sizing (Python, worst case over the small prime factors of `q`, exact prime-power losses): the
analytic argument with these constants needs `q ≥ 2^12.3` for `c = 3`, `2^16.9` for `c = 5/2`,
`2^21.1` for `c = 9/4` and `2^28.7` for `c = 2`. With the cruder bounds actually formalised
(`llp ≤ (l − ½ log p)²/2`, `β = l²/(2 log 17) + K/8`), `c = 11/4` fails just above `2^17` but
holds from `2^18` (so the finite check runs to `2^18`); `c = 5/2` would need `2^20`. Prime moduli work with `c = 1` from
`q ≈ 2600`; the certificates start at `2^12`.

## `L(1, χ)`: LLS Theorem 1.5 with weaker constants

For `χ` primitive mod `q ≥ 10¹⁰` (`χ ≠ 1`), `x ≥ 10⁵`, `l = log x`, `Z = Σ m_ρ/|ρ|²`:

1. `LLS.shifted_log_bound` (`LLS/L1/Shift.lean`): for `σ > 1`,
   `‖Σ_{n≤x} χΛ(n) n^{−σ} log(x/n) + (L'/L)(σ) log x + (L'/L)'(σ)‖ ≤ x^{1/2−σ} Z + 2x^{−σ}`.
2. `LLS.log_norm_L1_le` (`Integrate.lean`, LLS Lemma 2.5):
   `|log |L(1,χ)| − Re l1Sum χ x + Re (L'/L)(1)/l| ≤ (Z/√x + 2/x)/l²`.
3. `LLS.re_cesShift_ge`, `LLS.D_one_eq` (`CesLower.lean`): Lemma 2.3 from below with
   `EshiftLo x = −½(1−1/x) log π − γ/2 − log 2 − 1/x`; `Λ'/Λ(1) = G(1) + L'/L(1)`.
4. `LLS.l1Sum1_le`, `LLS.vonMangoldt_ces_le` (`Principal.lean`): `l1Sum1 x ≤ log l + γ − 1 + 3/l`
   (`x ≥ 10⁵`, via robin-rh's `mertens_RH`), `P₂(x) ≤ l − 1 + 1/x`.
5. `LLS.Z2_le_general`, `LLS.l1_core` (`Assembly.lean`), `LLS.log_norm_L1_le_c`,
   `LLS.neg_log_norm_L1_le_c` (`Weak.lean`): `±log |L(1,χ)| ≤ log l + γ + c/l` with `c` explicit.
6. `LLS.c_le`, `LLS.setup`, `LLS.final_exp` (`Final.lean`): `c ≤ 2.91 + 1.095 Zb/√x ≤ 4.11`,
   `x = 10⁵` or `⌊log² q⌋`, `e^{log l + γ + c/l} ≤ e^γ (l + c + c²/l) ≤ 2e^γ (log log q + 5)`.
   Headlines: `LLS.l1UpperBoundWith_of_GRH : L1UpperBoundWith 5`,
   `LLS.l1LowerBoundWith_of_GRH : L1LowerBoundWith 5`.

What the paper's constants would need: LLS Lemma 2.4 (`P₂(x) = l − 1 − γ + O(x^{−1/2})` under
RH, a shifted Cesàro formula for `ζ`), Lemma 2.6 (`l1Sum1 x = log l + γ − 1 + γ/l + O(x^{−1/2})`
under RH), Lemma 5.1 (`χ(p) = −1` is extremal) and `x = (log q)²/4` down to `x ≈ 132`; their
bound has a margin of about `0.004` at `q = 10¹⁰`.

## Bach's constant `2` (round 7)

1. `LLS.bach2_of_GRH : GRH → Ankeny.BachSubgroupBound 2`: `q ≤ 2` trivial; `3 ≤ q < 2^2500` by
   `LLS.good2_range` and `LLS.bach_of_good2`; `q ≥ 2^2500` by `LLS.goodQ_tail2` and
   `LLS.bach_of_goodQ`.
2. `LLS.keyP`: `LLS.key` with `log x − 2` replaced by any `Pc ≤ cesSum x`.
3. `LLS.budget_nonpos`: `base2 x Pc − κ log q − C ≤ 0` for every `C` bounding the prime costs;
   `budgetQ_nonpos` (`C = costQ x q = Σ_{p ∣ q, p ≤ x} W_p`) and `budgetU_nonpos`
   (`C = Σ_{p<53} max(0, W_p − β log p) + β log q`, `β = l²/(2 log 53) + 2K/52`, `β ≤ κ`).
4. `LLS.Check.checkChunk_sound`: `checkChunk m w lo hi = true → ∀ q ∈ [lo, hi), Good2 q`, from
   `blockOK_sound` (per block) and `go_sound` (the block loop). The interval bounds are
   `Side.core`, `Side.base`, `Side.Wp_le`, `Side.bet`, with the casts `cast_K1`, …, `cast_Wup`;
   `logLo_le`, `le_logHi`, `isPrimeB_iff`, `lamLo_le`, `cesLo_le` are the primitive facts.
5. Sizing (c = 2, this checker): the uniform budget holds on every block from `2^27` on; below
   that about 7,500 moduli fail the per-modulus budget (sum `≈ 4.4·10^9`, the largest
   `≈ 3.9·10^7`) and go to the generation search.

## LLS Theorem 1.1 with the paper's `B(q)` (round 9)

1. `LLS.Thm11.leastPrimeOutsideSubgroup_of_GRH : GRH → LeastPrimeOutsideSubgroup`
   (`LLS/Thm11/Main.lean`): `x = ⌊(log q + B(q))²⌋ ≥ 64`; if every prime `ℓ ≤ x` prime to `q`
   lies in `H`, `LLS.Thm11.exists_char_of_primes_mem` gives `χ ≠ 1` equal to `1` on every
   `n ≤ x` prime to `q`; `budget11` and `phi_pos` contradict each other.
2. `LLS.Thm11.sum_re_ge_max`, `keyM`, `budgetM_nonpos` (`Budget.lean`): `LLS.keyP` with the
   Cesàro lower bound `max(0, Pc − Lc_q) − Lc_R`. `budget11`:
   `base0(x) + 2K max(0, PcF(x) − σ(q)) − κ log q − ω(q) mC(x) − RC(x) ≤ 0` given `R5OK x`, with
   `PcF_le : PcF x ≤ cesSum x` (`Sharp.Hg_inv_bounds` for `x ≥ 100`, `vonMangoldt_ces_ge` below).
3. `LLS.Thm11.phi_pos` (`Elim.lean`): from `log q + B(q) < √(x+1) ≤ ν(x)`, `F1 x > 0` and
   (when `ν − 3 − 2 log 8 ≥ 8`) `F2 x 8 > 0`, `F2 x (ν − 3 − 2 log 8) > 0`, the budget is
   positive. Case `σ ≤ 2 log L − 8/5`: multiplier `K` for `2σ` and `u = 2ω(log L)²/L`; the bound
   decreases in `L`, evaluated at `L = ν`. Case `σ > 2 log L − 8/5`: multiplier
   `μ = 2 mC ν/(log x)²` for `u`; concave in `L`, evaluated at the ends. `mul_log_sq_le`:
   `a (log b)² ≤ b (log a)²` for `8 ≤ a ≤ b`.
4. `F1_eq`, `F2a_eq`, `F2b_eq` (`NumCore.lean`): exact decompositions `s·Q + δ·W + V`;
   `F1_ge`, `F2a_ge`, `F2b_ge`, `R5_of`: rational lower bounds on a box from `InBox`
   (`inBox_of_data`: `2^{k_a} ≤ X_a^{64}`, `X_b^{64} ≤ 2^{k_b}`, `s_a² ≤ X_a`, `X_b ≤ s_b²`).
5. `Boxes.lean`: `f1_range`, `f2a_range`, `f2b_range`, `r5_range` for `x < 10^16` (2 + 8, 15,
   23 and 6 boxes); `Tail.lean`: `F1_tail`, `F2a_tail`, `F2b_tail`, `R5_tail` for
   `x ≥ 10^16` (`tail_facts`: `l² ≤ √x/100`, `l ≤ √x/10^4`).
6. Part 2, `LLS.Thm11.leastPrimeOutsideSubgroupRough_of_GRH` (`Rough.lean`): `Phi1_nonpos_rough`
   (`LLS.Phi1_nonpos` for moduli whose prime factors are all `≥ x`, via `llp_eq_zero_of_le`,
   `lcp_eq_zero_of_le`) and `goodP_ge_3000` (`IvR.goodP_rough` for `3000 ≤ q < 4096`, then the
   existing intervals and tail).


## LLS Theorem 1.4 with the paper's bound (round 10)

1. `LLS.Thm14.leastPrimeInCoset_of_GRH : GRH → LeastPrimeInCoset` (`LLS/Thm14/Main.lean`):
   `u = h − 1`, `B = Bf u (log q)`, `s = max 31622 ⌊B⌋₊`, `N = ⌊7072s/10000⌋ + 1` (so
   `s² ≤ 2N²`). If no prime `p ≤ s²` lies in `aH`, `main_ineq` holds, and `reduce` with
   `star_small` (`B < 31622`) or `star_large` (`B ≥ 31622`) contradicts it. `omega_le`:
   `ω(q) ≤ 10 + log q/log 30`; `llp_le_two`; `card_Htil_le`.
2. `LLS.Thm14.Htil`, `card_Htil_le`, `sum_Htil_unit`, `sum_Htil_coset`,
   `re_sum_Htil_ne_one_ge` (`Orth.lean`), from `CommGroup.exists_apply_ne_one_of_hasEnoughRootsOfUnity`
   and `CommGroup.card_monoidHom_of_hasEnoughRootsOfUnity` on `G ⧸ H`.
3. `LLS.Thm14.psiLog_le` (`PsiUp.lean`): `Σ_{n ≤ x} Λ(n) log(x/n) ≤ x + (3/20)√x + 4 log x + 2`.
   `LLS.Thm14.sum_sq_pp_le` (`Squares.lean`): the prime powers `p^k ≤ s²`, `k ≥ 2`, through
   `halfPow n = p^{⌊k/2⌋}`, injective on even and on odd exponents.
4. `LLS.Thm14.norm_logGamma_le`, `norm_shiftGamma_le` (`Gamma.lean`); `shift_complex`,
   `maxV_le`, `norm_logSum_le` (`Prim.lean`).
5. `LLS.Thm14.norm_diff_le`, `prime_cost`, `bad_cost`, `norm_logSum_char` (`PerChar.lean`).
6. `LLS.Thm14.main_ineq` (`Assembly.lean`).
7. `LLS.Thm14.reduce`, `reduceR`, `Pc_le` (`Reduce.lean`); `Bf`, `Phi2`, `cell_of`, `lam_of`
   (`CellCore.lean`); `Cells.box_all` (`Cells.lean`, 65 nodes, 33 leaves); `tail_u`, `tail_L`
   (`Tails.lean`); `phi2_all`, `star_small`, `star_large` (`Elim.lean`).
