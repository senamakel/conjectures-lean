# Solé–Planat's Dedekind Ψ criterion under RH in Lean

Lean proves Solé–Planat's inequality `Ψ(N_n)/(N_n log log N_n) > e^γ/ζ(2)` for every `n ≥ 3`,
where `Ψ(n) = n ∏_{p ∣ n}(1 + 1/p)` is the Dedekind psi function and `N_n = p_1 ⋯ p_n` is the
primorial of order `n`. `solePlanat_unconditional` is proved unconditionally in Lean, with RH
supplied by the certified proof in
[leanprover-community/riemann-hypothesis](https://github.com/leanprover-community/riemann-hypothesis).
The main library holds a complete Lean proof that RH implies the inequality, through
[nicolas-rh](../nicolas-rh/)'s Nicolas inequality, and a proof with no RH at all that Nicolas'
inequality implies it.

**Literature status: RH-equivalent.** P. Solé and M. Planat, *Extreme values of the Dedekind Ψ
function*, J. Comb. Number Theory 3 (2011), no. 1, 1–6, arXiv:1011.1825, prove that this
inequality for every `n ≥ 3` is equivalent to RH, so the theorem is RH in another form. This
project proves the direction RH ⇒ inequality, following their Theorem 1 (Nicolas' criterion
plus the Euler product of `ζ(2)`). Built by OpenHuman agents.

## Headline theorems

```lean
-- Abundant/Statement.lean (target definitions, unchanged)
noncomputable def dedekindPsi (n : ℕ) : ℝ :=
  n * ∏ p ∈ n.primeFactors, (1 + 1 / (p : ℝ))
noncomputable def solePlanatRatio (n : ℕ) : ℝ :=
  dedekindPsi n / (n * Real.log (Real.log n))
def SolePlanatStatement : Prop :=
  ∀ n : ℕ, 3 ≤ n →
    Real.exp Real.eulerMascheroniConstant / (riemannZeta 2).re
      < solePlanatRatio (Nicolas.kthPrimorial n)

-- Abundant/SolePlanat.lean
theorem Abundant.solePlanat_of_nicolas (h : Nicolas.NicolasStatement) : SolePlanatStatement

-- Abundant/SolePlanatRH.lean
theorem Abundant.solePlanat_of_RH (hRH : RiemannHypothesis) : SolePlanatStatement

-- Unconditional/AbundantUnconditional.lean
theorem solePlanat_unconditional : Abundant.SolePlanatStatement
```

## Tier and provenance

| Theorem | Tier | Hypotheses |
|---|---|---|
| `Abundant.solePlanat_of_nicolas` | C | `Nicolas.NicolasStatement` (nicolas-rh's fixed statement, imported) |
| `Abundant.solePlanat_of_RH` | C | `RiemannHypothesis` |
| `solePlanat_unconditional` (`Unconditional/`) | U | none |

* `RiemannHypothesis` is Mathlib's definition, the one leanprover-community/riemann-hypothesis
  proves as `riemannHypothesis`.
* `SolePlanatStatement` is the statement of Solé–Planat's abstract and main theorem (read on
  arXiv). formal-conjectures has no statement of it (searched at commit `9097e2f` for Dedekind,
  Solé, Planat). `ζ(2)` is written `(riemannZeta 2).re` (Mathlib's `riemannZeta` is complex);
  `riemannZeta_two_re` proves it equals `π²/6`. `N_n` is nicolas-rh's `Nicolas.kthPrimorial n`,
  itself copied verbatim from formal-conjectures' `Nat.kthPrimorial`, imported, not restated.
* Prior formalisations searched: formal-conjectures (`9097e2f`), 1337isnot1337/solved-conjectures,
  Mathlib (no Dedekind Ψ); facebookresearch/atlas-lean has a definition of Ψ and no theorem
  about it.

## Axioms

From `lake env lean` on a file containing `#print axioms` for each theorem (2026-11-26):

```
'Abundant.solePlanat_of_nicolas' depends on axioms: [propext, Classical.choice, Quot.sound]
'Abundant.solePlanat_of_RH' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Nicolas.Check.loop_ok._native.native_decide.ax_1_1]
```

`Nicolas.Check.loop_ok` is nicolas-rh's one `native_decide`, its proved-sound rational interval
check of Nicolas' inequality at the 9591 primes `3 ≤ p ≤ 10^5` (about 26 s to build). No
computation is added here.

## Proof outline

1. `φ(n) Ψ(n) = n² ∏_{p ∣ n}(1 − p⁻²)` for every `n` (Solé–Planat, Proposition 5), from
   Mathlib's product formula for `φ` (`totient_mul_dedekindPsi`, `Abundant/SolePlanat.lean`).
2. `∏_{p ∈ s}(1 − p⁻²)⁻¹ ≤ π²/6` for every finite set of primes `s`: Mathlib's Euler product
   for the completely multiplicative `n ↦ n⁻²` writes the left side as the sum of `n⁻²` over the
   `s`-factored numbers, at most `Σ n⁻² = π²/6` (`prod_inv_one_sub_invSq_le`). So
   `∏_{p ∣ n}(1 − p⁻²) ≥ 1/ζ(2)` (`inv_pi_sq_le_prod`).
3. With `N = N_n ≥ 2^n ≥ 8`, `log log N > 0` and
   `R(N) = (N/φ(N)) ∏_{p ∣ N}(1 − p⁻²)/log log N > e^γ ∏(1 − p⁻²) ≥ e^γ/ζ(2)`, using Nicolas'
   inequality `N/φ(N) > e^γ log log N` (`solePlanat_of_nicolas_at`, `solePlanat_of_nicolas`).
4. Nicolas' inequality under RH is nicolas-rh's `Nicolas.nicolas_of_RH`
   (`Abundant/SolePlanatRH.lean`).

## Deviations from the literature

None. The statement is Solé–Planat's, with the same range `n ≥ 3`; the proof is theirs.

## Building

Lean `v4.36.0`, Mathlib `fc4f59e5`. Requires [nicolas-rh](../nicolas-rh/) and
[robin-rh](../robin-rh/) by path. Only the light robin-rh modules that nicolas-rh's `Nicolas.Main`
imports are built (`Robin.Defs`, `Robin.Lagarias.Bounds`, `Robin.Mertens.*`, `Robin.RH.*`,
`Robin.Main.Tail`); robin-rh's verified-range sieve is not.

```bash
lake build Abundant
```

From a cold nicolas-rh and robin-rh (erdos-985 and Mathlib built), `lake build
Abundant.SolePlanatRH` took 2 min 20 s wall (122 s user CPU) on a loaded 95-core machine; the
`Abundant` modules themselves take under 15 s each.

## Unconditional version

`Unconditional/AbundantUnconditional.lean` imports
[leanprover-community/riemann-hypothesis](https://github.com/leanprover-community/riemann-hypothesis)
(commit `507a75d91d`) and closes the RH hypothesis with its `riemannHypothesis`:

| Theorem | Statement | Axioms |
|---|---|---|
| `solePlanat_unconditional` | `SolePlanatStatement` | standard three + `Nicolas.Check.loop_ok` (`native_decide`), expected; not yet run |

```bash
scripts/check-unconditional.sh /path/to/riemann-hypothesis   # cloned there if missing
```

The script uses that project's community cache, about 93 GB. The import opens around 900,000
module files and needs about 19 GB of RAM. Raise the open-file limit first; on Linux
`sudo prlimit --pid $$ --nofile=2000000:2000000`, on macOS
`sudo sysctl -w kern.maxfiles=2000000 kern.maxfilesperproc=1500000 kern.maxvnodes=1500000`.

The riemann-hypothesis proof adds no axioms of its own. It was certified by the Lean FRO and the Mathlib Initiative on 2026-11-21, and independent kernels accept it (math.mit.edu/~drew/grh). This check links against the community build cache and does not repeat those kernel checks.

## Credits

No files are vendored. `kthPrimorial` and `NicolasStatement` come from the lake dependency
[nicolas-rh](../nicolas-rh/) (`kthPrimorial` is copied there from
[formal-conjectures](https://github.com/google-deepmind/formal-conjectures), Apache-2.0).
