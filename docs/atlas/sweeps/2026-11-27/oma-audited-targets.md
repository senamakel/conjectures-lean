# First attack on the OMA audit shortlist

27 November 2026. The live registry pinned Formal Conjectures at
`9097e2f90e66d2f6244209cb1c07f7120d17ec53`, Lean `v4.33.1` and Mathlib
`0df444a`. The separate OMA checkout used upstream revision
`734b11132537c54ea4052b09dad34a56f89bb4c0`.

| Candidate | Discovery decision |
| --- | --- |
| `Erdos770.erdos_770.parts.iii.R1.H2` | The exact claim is that for every prime `q < 2^17` and proper subgroup of `(ZMod q)ˣ`, there is a unit outside it with least residue at most `(21/5) log² q`. The brief showed zero agents and an unresolved step. GitHub's open-PR list then found two accepted Lean checks awaiting human review. An initial scratch port replaced exhaustive group generation with a search for a primitive root using prime factors of `q − 1`; the first compile stopped at an unbuilt reduction import. Set aside the duplicate before any range computation. [Brief](https://lefttosolve.com/p/Erdos770.erdos_770.parts.iii.R1.H2/agent.txt) · [PR #1654](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/1654) · [PR #2792](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/2792) |
| `Erdos770.erdos_770.parts.iii.R1.H1` | Same constant and quantifiers for primes `q ≥ 2^17`. The brief reports zero agents and GitHub's open and closed PR search returned no matching H1 submission. The local large-modulus theorem needs the Dirichlet GRH nonvanishing premise and a long analytic dependency chain. Exa found a published QRH route and a GRH argument by MacKenzie for part (iii). Neither supplies a single-file OMA proof of H1. [Brief](https://lefttosolve.com/p/Erdos770.erdos_770.parts.iii.R1.H1/agent.txt) · [Original problem](https://www.erdosproblems.com/770) · [QRH note](https://doi.org/10.5281/zenodo.23608372) · [MacKenzie preprint](https://zenodo.org/records/24409350) |
| `RiemannHypothesis.robin_criterion.R1.H1` | The step is RH implying Robin's inequality for every natural integer `n > 5040`. The local proof of that exact direction relies on a verified range with 624 compiler-assisted checks. The range is the immediate blocker to an OMA port. [Brief](https://lefttosolve.com/p/RiemannHypothesis.robin_criterion.R1.H1/agent.txt) · [Reduction](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/3261) |

The local transcript search for `Erdos770.erdos_770.parts.iii` and `BachSubgroupBound`
recovered the existing subgroup-bound dependency. LivingBrain's matching notes
pointed to OMA #1280 and the `21/5` large-modulus argument. The source files
confirmed both. LemmaGraph exposed `ZMod.orderOf_units_dvd_card_sub_one` and
primitive-root lemmas for the finite-check approach.

Cookson and Flint Hills also have checked H2 submissions in human review.
Their H1 is the same eventual Diophantine lower bound for π, which remains
an import and portability problem at the OMA pin. [Cookson H2 #2853](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/2853) · [Flint H2 #2839](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/2839)

## Sun catalogue intake

A live catalogue search for `238165` returned no row. OMA's pinned A038107
entry concerns fractional parts of sums of reciprocals. The paper
inequalities are separate targets. The Exa query for `Sun conjecture 2.7 (i)
A238165 pi(kn) pi((k+1)n) monotonicity proof arXiv 1402.6641 Lean` located
earlier Lean proofs in F8Labs' Apache-2.0 repository, pinned below. The proof
of 2.7(i) covers all positive `k`, including the paper's endpoint `k = n`.
The proof of 2.14(ii) gives each adjacent inequality for `n ≥ 3`. The OEIS
A038107 comment also asks for the limit 1. The workspace has a separate
theorem for that combined statement. [Sun's paper, v12](https://arxiv.org/abs/1402.6641v12) · [A238165](https://oeis.org/A238165) · [A038107](https://oeis.org/A038107) · [Different OMA target](https://lefttosolve.com/p/OeisA38107.conjecture) · [F8Labs 2.7(i)](https://github.com/F8Labs-ai/sun_conjectures/blob/388a290aea68b0e59fa767d23a4ab296c592432d/SunConjectures/SunComplete.lean#L677) · [F8Labs 2.14(ii)](https://github.com/F8Labs-ai/sun_conjectures/blob/388a290aea68b0e59fa767d23a4ab296c592432d/SunConjectures/SunSquares.lean#L892)

The following exact paper statements and adapters compile on the OMA pin.
Both adapters use `propext`, `Classical.choice` and `Quot.sound`.
They establish the statement match given the corresponding F8Labs
theorem types. The upstream proofs themselves were written for a
newer Mathlib.

```lean
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace SunCatalogue

def paperTwoSeven : Prop :=
  ∀ n : ℕ, 4 < n → ∀ k : ℕ, 1 ≤ k → k ≤ n →
    (Nat.primeCounting ((k + 1) * n) : ℝ) ^ (1 / ((k : ℝ) + 1)) <
      (Nat.primeCounting (k * n) : ℝ) ^ (1 / (k : ℝ))

def paperTwoFourteen : Prop :=
  StrictAntiOn (fun n : ℕ => (Nat.primeCounting (n ^ 2) : ℝ) ^ (1 / (n : ℝ))) (Set.Ici 3)

theorem paperTwoSeven_of_all_k
    (h : ∀ n k : ℕ, 5 ≤ n → 1 ≤ k →
      (Nat.primeCounting ((k + 1) * n) : ℝ) ^ (1 / ((k : ℝ) + 1)) <
        (Nat.primeCounting (k * n) : ℝ) ^ (1 / (k : ℝ))) : paperTwoSeven := by
  intro n hn k hk _
  exact h n k hn hk

theorem paperTwoFourteen_of_successor
    (h : ∀ n : ℕ, 3 ≤ n →
      (Nat.primeCounting ((n + 1) ^ 2) : ℝ) ^ (1 / ((n : ℝ) + 1)) <
        (Nat.primeCounting (n ^ 2) : ℝ) ^ (1 / (n : ℝ))) : paperTwoFourteen := by
  let f (n : ℕ) := (Nat.primeCounting (n ^ 2) : ℝ) ^ (1 / (n : ℝ))
  have ha : StrictAnti (fun n : ℕ => f (n + 3)) := by
    apply strictAnti_nat_of_succ_lt
    intro n
    simpa only [f, show n + 1 + 3 = n + 3 + 1 by omega, Nat.cast_add, Nat.cast_one]
      using h (n + 3) (by omega)
  intro i hi j hj hij
  have hii : i - 3 + 3 = i := by simp only [Set.mem_Ici] at hi; omega
  have hjj : j - 3 + 3 = j := by simp only [Set.mem_Ici] at hj; omega
  simpa only [hii, hjj, f] using ha (show i - 3 < j - 3 by omega)


end SunCatalogue
```

OMA's linter requires an existing text-only ID for a statement submission.
These entries therefore need catalogue intake, or a Formal Conjectures
statement and a later catalogue refresh. A known-result record can cite the
existing formal proof and preserve the correct provenance. [OMA linter](https://github.com/GuillaumeBAUD-coder/open-math-agents/blob/734b11132537c54ea4052b09dad34a56f89bb4c0/tools/lint.py) · [Formal Conjectures contribution rules](https://github.com/google-deepmind/formal-conjectures/blob/main/CONTRIBUTING.md)

The search for the final Gawron–Miska–Ulas wording located the publisher's
article and the preprint. The available publisher abstract does not
establish whether the conjecture survived peer review. The exact local
refutation remains tied to the preprint pending a full-text comparison.
[Publisher record](https://doi.org/10.1007/s00605-017-1041-2) · [Preprint v1](https://arxiv.org/abs/1703.01955v1)
