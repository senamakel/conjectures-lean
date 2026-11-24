# Nicolas' inequality under RH in Lean

Lean proves Nicolas' inequality `N_k/φ(N_k) > e^γ log log N_k` for every `k ≥ 1`, where
`N_k = p_1 ⋯ p_k` is the product of the first `k` primes. `nicolas_unconditional` is proved
unconditionally in Lean, with RH supplied by the certified proof in
[leanprover-community/riemann-hypothesis](https://github.com/leanprover-community/riemann-hypothesis).
The main library holds a complete Lean proof that RH implies the inequality for every `k ≥ 1`,
with the 9591 primes `3 ≤ p ≤ 10^5` covered by a proved-sound interval checker.

**Literature status: RH-equivalent.** Nicolas (*Petites valeurs de la fonction d'Euler*,
J. Number Theory 17 (1983) 375-388) proved that RH is equivalent to this inequality for all
`k ≥ 1` (see also Nicolas, Acta Arith. 155 (2012)), so the theorem is RH in another form.
Nicolas also showed that if RH fails, the inequality holds for infinitely many `k` and fails
for infinitely many. This repository proves the direction RH ⇒ inequality.

## Headline theorem

```lean
-- Nicolas/Statement.lean (target definitions, unchanged)
noncomputable def kthPrimorial (k : ℕ) : ℕ :=
  ∏ i ∈ Finset.range k, Nat.nth Nat.Prime i
def NicolasStatement : Prop :=
  ∀ k : ℕ, 1 ≤ k →
    Real.exp Real.eulerMascheroniConstant * Real.log (Real.log (kthPrimorial k))
      < (kthPrimorial k : ℝ) / (Nat.totient (kthPrimorial k) : ℝ)

-- Nicolas/Main.lean
theorem Nicolas.nicolas_of_RH (hRH : RiemannHypothesis) : NicolasStatement

-- Unconditional/NicolasUnconditional.lean
theorem nicolas_unconditional : Nicolas.NicolasStatement
```

## Tier and provenance

| Theorem | Tier | Hypotheses |
|---|---|---|
| `Nicolas.nicolas_of_RH` | C | `RiemannHypothesis` |
| `nicolas_unconditional` (`Unconditional/`) | U | none |

* `RiemannHypothesis` is Mathlib's definition, the one leanprover-community/riemann-hypothesis
  proves as `riemannHypothesis`.
* formal-conjectures has no statement of Nicolas' criterion (checked at commit `86a2f58a`;
  `FormalConjectures/Paper/RiemannHypothesisEquivalents.lean` has Robin, Lagarias, Li,
  Beurling–Nyman and Weil, not Nicolas). `kthPrimorial` is copied verbatim from
  formal-conjectures' `Nat.kthPrimorial`
  (`FormalConjecturesForMathlib/Data/Nat/Prime/Nth.lean`). `NicolasStatement` is the statement
  of Nicolas (1983).
* No cited computation is assumed: the range `p_k ≤ 10^5` is checked in Lean.

## Axioms

From `lake env lean` on a file containing `#print axioms Nicolas.nicolas_of_RH` (2026-11-24,
this commit):

```
'Nicolas.nicolas_of_RH' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Nicolas.Check.loop_ok._native.native_decide.ax_1_1]
```

`Nicolas.Check.loop_ok` is one `native_decide`: it walks `n = 1, …, 10^5` in `ℚ`, keeping a
rounded-down `R ≤ ∏_{p≤n} p/(p−1)` and a rounded-up `T ≥ θ(n)`, and checks
`EU · logUp T < R` at each of the 9591 primes `3 ≤ p ≤ 10^5`, with `EU ≥ e^γ` and
`logUp T ≥ log T` (40-term series for `log`, rounding to `2^{−64}`). Its soundness is
`Nicolas.Check.finite_range` (`Nicolas/Check/Sound.lean`). The module builds in about 26 s.

`lake build NicolasChecks` pins this list with `#guard_msgs` and fails if the theorem picks up
another axiom (for example `sorryAx`).

## Proof outline

Full blueprint with every Lean statement and constant: [`docs/BLUEPRINT.md`](docs/BLUEPRINT.md).
Put `q = p_k`, `S(x) = Σ_{p≤x} c_p` with `c_p = −log(1 − 1/p)`, `w(t) = (1 + log t)/(t² log² t)`.

1. `N_k = q#`, `log N_k = θ(q)`, `N_k/φ(N_k) = exp S(q)` (`Nicolas/Primorial.lean`). The claim
   is `γ + log log θ(q) < S(q)`.
2. Mertens as an identity (`Nicolas/Mertens.lean`):
   `S(x) = γ + log log x + (θ(x) − x)/(x log x) + J(x) − T(x)`, `J(x) = −∫_x^∞ (θ − t) w`,
   `0 ≤ T(x) = Σ_{p>x}(c_p − 1/p) ≤ 4/x`; and `log log θ(x) ≤ log log x + (θ(x) − x)/(x log x)`.
   The secondary terms cancel, so `S(x) − γ − log log θ(x) ≥ J(x) − T(x)`.
3. `∫_x^∞ (t − ψ) w ≥ −(0.338 + 17.9 x^{−1/2})/(√x log x)` by parts against `Ψ₁ − t²/2`, whose
   RH bound `t^{3/2}/20 + 4t` comes from erdos-985 through robin-rh (`Nicolas/Tail.lean`).
4. `ψ(t) − θ(t) ≥ ψ(√t) ≥ 0.68 √t`, unconditional, and `∫_x^∞ √t w ≥ (12/13)·2/(√x log x)`.
5. For `x ≥ 10^5`: `J(x) ≥ 0.86/(√x log x) > 4/x ≥ T(x)` (`Nicolas/Analytic.lean`).
6. For `3 ≤ q ≤ 10^5`: the finite check above. `q = 2`: `log log 2 < 0`.

## Layout

| File | Content |
|---|---|
| `Nicolas/Statement.lean` | target statement (do not edit) |
| `Nicolas/Primorial.lean` | step 1 |
| `Nicolas/Mertens.lean` | step 2 |
| `Nicolas/Tail.lean` | steps 3 and 4, `tail_lower` |
| `Nicolas/Analytic.lean` | step 5, `sum_cp_gt_large` |
| `Nicolas/Check/Defs.lean` | the checker (computable) |
| `Nicolas/Check/Sound.lean` | its soundness and the `native_decide` |
| `Nicolas/Main.lean` | `nicolas_of_RH` |
| `NicolasChecks/Axioms.lean` | `#guard_msgs` axiom allow-list |
| `Unconditional/NicolasUnconditional.lean` | RH discharged by riemann-hypothesis |

## Deviations from the literature

* None in the statement. The proof differs from Nicolas': he uses Rosser–Schoenfeld's explicit
  bounds for `θ` and the zero sum `Σ 1/(ρ(1−ρ)) = 2 + γ − log 4π`. Here the only RH input is
  erdos-985's integrated bound `|Ψ₁(t) − t²/2| ≤ t^{3/2}/20 + 4t` (as in robin-rh), and
  `ψ − θ` is bounded below unconditionally. This gives an analytic threshold of `10^5`, and the
  primes below it are checked by computation.
* The finite range is limited by the bound `γ < 0.5774` from erdos-985: the slack of the
  inequality near `p` is about `2/(√p log p)` (`5.8·10^{−4}` at `p ≈ 10^5`,
  `1.5·10^{−4}` at `p ≈ 10^6`), and the `γ` bound loses `1.84·10^{−4}`.

## Building

Lean `v4.36.0`, Mathlib `fc4f59e5` (through erdos-985 `9538edb`), robin-rh `dfa8d63` (`main`).
Only robin-rh modules that do not depend on its `Robin/Small.lean` are imported.

```bash
lake exe cache get
lake build Nicolas NicolasChecks
```

With the dependencies built, the `Nicolas` library builds in 1 min 26 s wall (66 s CPU) on a
95-core machine; the slowest modules are `Nicolas.Tail` (27 s) and `Nicolas.Check.Sound` (26 s,
including the `native_decide`).

## Unconditional version

`Unconditional/NicolasUnconditional.lean` imports
[leanprover-community/riemann-hypothesis](https://github.com/leanprover-community/riemann-hypothesis)
(commit `507a75d91d`) and closes the RH hypothesis with its `riemannHypothesis`:

| Theorem | Statement | Axioms |
|---|---|---|
| `nicolas_unconditional` | `NicolasStatement` | standard three + `Nicolas.Check.loop_ok` (`native_decide`) |

Output of `scripts/check-unconditional.sh` on 2026-11-24 (commit `8be0212`, riemann-hypothesis
`507a75d91d` linked from its community cache; 29 min wall, mostly waiting for a free RAM slot):

```
'nicolas_unconditional' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Nicolas.Check.loop_ok._native.native_decide.ax_1_1]
```

```bash
scripts/check-unconditional.sh /path/to/riemann-hypothesis   # cloned there if missing
```

The script uses that project's community cache, about 93 GB. The import opens around 900,000
module files and needs about 19 GB of RAM. Raise the open-file limit first; on Linux
`sudo prlimit --pid $$ --nofile=2000000:2000000`, on macOS
`sudo sysctl -w kern.maxfiles=2000000 kern.maxfilesperproc=1500000 kern.maxvnodes=1500000`.

The riemann-hypothesis proof adds no axioms of its own. It was certified by the Lean FRO and the Mathlib Initiative on 2026-11-21, and independent kernels accept it (math.mit.edu/~drew/grh). This check links against the community build cache and does not repeat those kernel checks.

## Credits

No files are vendored. `kthPrimorial` is copied from
[formal-conjectures](https://github.com/google-deepmind/formal-conjectures) (commit `86a2f58a`,
Apache-2.0). The explicit formula and the bounds on Euler's constant come from the lake
dependency [erdos-985](https://github.com/senamakel/erdos-985); the Mertens identity, `Ψ₁`
machinery and certified `exp` bounds from [robin-rh](https://github.com/senamakel/robin-rh).
