import Mathlib

/-!
# Statements for Erdős #142 (variant `lower`) and the all-`k` form of Erdős #140

Three groups of definitions, each copied word for word from its source.

**formal-conjectures** (Apache-2.0, © 2025 The Formal Conjectures Authors), commit
`9097e2f90e66d2f6244209cb1c07f7120d17ec53`:

* `Set.IsAPOfLengthWith`, `Set.IsAPOfLength`, `Set.IsAPOfLengthFree`,
  `Set.IsAPOfLengthFree.maxCard`: `FormalConjecturesForMathlib/Combinatorics/AP/Basic.lean`.
* `Erdos142.r` and `Erdos142.VariantsLower`: `FormalConjectures/ErdosProblems/142.lean`,
  `Erdos142.r` and theorem `erdos_142.variants.lower` (`research open` there). The theorem
  `erdos_142.variants.lower (k : ℕ) (hk : 1 < k) : P := by sorry` becomes
  `def VariantsLower : Prop := ∀ (k : ℕ) (hk : 1 < k), P`, with `P` unchanged.

**Ours**: `Erdos140.AllK`. formal-conjectures has no file for Erdős #140 at `9097e2f`. Open
PR google-deepmind/formal-conjectures#6660 states only `k = 3`, as
`(fun N : ℕ => (r3 N : ℝ)) =O[atTop] (fun N : ℕ => (N : ℝ) / Real.log N ^ C)` for `0 < C`.
`Erdos140.AllK` is our statement of the all-`k` form ([ErGr80], [Er81]): the same shape, with
`r3` replaced by formal-conjectures' `Erdos142.r k` for every `k ≥ 3`.

**openai/math** (Apache-2.0, © OpenAI), commit `adc7f1241b42e322a6451854ab7e4b4c146bf78a`,
file `lean/OAI/Combinatorics/Progressions/Model.lean`, namespace `OAI.Erdos3`:
`HasAP`, `APFree`, `extremalNumber`, `QuantitativeDensityBound`, `QuantitativeDensityTheorem`.
They are copied verbatim into the namespace `Erdos142.OAI` (renamed only to avoid clashing with
openai/math's own names if both are ever imported). openai/math proves
`OAI.Erdos3.manuscriptQuantitativeDensityTheorem : QuantitativeDensityTheorem` in
`lean/OAI/Combinatorics/Progressions/Results/Conclusions.lean` (Lean `v4.34.1`, Mathlib
`d13f23b7`). Here it is a tier-H hypothesis.
-/

section FormalConjecturesAP

variable {α : Type*} [AddCommMonoid α]

/--
A set $S$ is an arithmetic progression of length $l$ with first term $a$ and difference $d$
if $S = \{a, a + d, ..., a + (l - 1)d\}$, if $l$ if finite, else $S = \{a, a + d, a + 2d, ...\}.
This can be written as `s.IsAPOfLengthWith l a d`, where `l : ℕ∞` may take the infinite
value `⊤`.
-/
def Set.IsAPOfLengthWith (s : Set α) (l : ℕ∞) (a d : α) : Prop :=
  ENat.card s = l ∧ s = {a + n • d | (n : ℕ) (_ : n < l)}

/--
The predicate that a set `s` is an arithmetic progression of length `l` (possibly infinite).
This predicate does not assert a specific value for the first term or the difference of the
arithmetic progression.
-/
def Set.IsAPOfLength (s : Set α) (l : ℕ∞) : Prop :=
  ∃ a d : α, s.IsAPOfLengthWith l a d

/-- We say that a set `s` is free of arithmetic progressions of length `l` if `s` contains no
non-trivial arithmetic progressions of length `l`. Written as `Set.IsAPOfLengthFree s l`. --/
def Set.IsAPOfLengthFree (s : Set α) (l : ℕ∞) : Prop :=
  ∀ t ⊆ s, t.IsAPOfLength l → l ≤ 1

/--
Define the largest possible size of a subset of $\{1, \dots, N\}$ that does not contain
any non-trivial $k$-term arithmetic progression.
-/
noncomputable def Set.IsAPOfLengthFree.maxCard (k : ℕ) (N : ℕ) : ℕ :=
  sSup {Finset.card S | (S) (_ : S ⊆ Finset.Icc 1 N) (_ : (S : Set ℕ).IsAPOfLengthFree k)}

end FormalConjecturesAP

open Asymptotics Filter

namespace Erdos142

noncomputable abbrev r := Set.IsAPOfLengthFree.maxCard

/--
Show that $r_k(N) = o_k(N / \log N)$, where $r_k(N)$ the largest possible size of a subset
of $\{1, \dots, N\}$ that does not contain any non-trivial $k$-term arithmetic progression.

formal-conjectures `erdos_142.variants.lower`, `@[category research open, AMS 11]`.
-/
def VariantsLower : Prop :=
  ∀ (k : ℕ) (hk : 1 < k),
    (fun N => (r k N : ℝ)) =o[atTop] (fun N : ℕ => N / (N : ℝ).log)

/-! ### openai/math definitions (`OAI.Erdos3`, `Progressions/Model.lean`, verbatim) -/

namespace OAI

def HasAP (A : Set ℕ) (k : ℕ) : Prop :=
  ∃ a d : ℕ, 0 < d ∧ ∀ i < k, a + i * d ∈ A

def APFree (A : Set ℕ) (k : ℕ) : Prop := ¬ HasAP A k

noncomputable def extremalNumber (k N : ℕ) : ℕ := by
  classical
  exact (((Finset.Icc 1 N).powerset).filter fun S : Finset ℕ ↦ APFree (S : Set ℕ) k).sup
    Finset.card

def QuantitativeDensityBound (k : ℕ) : Prop :=
  ∃ C c η : ℝ, 0 < C ∧ 0 < c ∧ 0 < η ∧
    ∀ N : ℕ, 3 ≤ N →
      (extremalNumber k N : ℝ) ≤
        C * N * Real.exp (-c * (Real.log (Real.log N)) ^ (1 + η))

def QuantitativeDensityTheorem : Prop :=
  ∀ k : ℕ, 3 ≤ k → QuantitativeDensityBound k

end OAI

end Erdos142

namespace Erdos140

/-- **Our statement** (no formal-conjectures file exists): the all-`k` form of Erdős #140,
$r_k(N) \ll_{k,C} N / (\log N)^C$ for every $k \ge 3$ and every $C > 0$. Same shape as the
`k = 3` statement `erdos_140` of formal-conjectures PR #6660, with formal-conjectures'
`Erdos142.r k` in place of `r3`. -/
def AllK : Prop :=
  ∀ (k : ℕ), 3 ≤ k → ∀ (C : ℝ), 0 < C →
    (fun N : ℕ => (Erdos142.r k N : ℝ)) =O[atTop] (fun N : ℕ => (N : ℝ) / Real.log N ^ C)

end Erdos140
