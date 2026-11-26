import Mathlib

/-!
# Exceptional sets for Legendre, Oppermann, Andrica and Brocard (target statements: do not change)

The four conjectures are copied from google-deepmind/formal-conjectures, commit `9097e2f`
(Apache-2.0, see `NOTICE`):

* `LegendreConjecture.legendre_conjecture`, `FormalConjectures/Wikipedia/LegendreConjecture.lean`;
* `Oppermann.oppermann_conjecture`, `FormalConjectures/Wikipedia/Oppermann.lean`;
* `Andrica.andrica_conjecture`, `FormalConjectures/Wikipedia/Andrica.lean`;
* `Brocard.brocard_conjecture`, `FormalConjectures/Wikipedia/BrocardConjecture.lean`.

The bodies are verbatim. The `theorem … := by sorry` wrappers became `def … : Prop :=`, and each
conjecture is split into its per-index body (`LegendreAt n`, …), so that it reads
`∀ n ≥ 1, LegendreAt n` (proved by `rfl` below for each of the four). All four conjectures are
open and this project does not prove them.

The targets of this project are the exceptional sets: the indices `n ≤ N` at which the
per-index statement fails. Each target says that the exceptional set has `O(log³ N)` elements.
-/

open Finset Filter

namespace LegendreExceptions

/-! ## The conjectures, verbatim from formal-conjectures -/

/-- `LegendreConjecture.legendre_conjecture`: a prime between consecutive squares. -/
def LegendreConjecture : Prop :=
    ∀ n ≥ 1, ∃ p ∈ Set.Ioo (n ^ 2) ((n + 1) ^ 2), Nat.Prime p

/-- `Oppermann.oppermann_conjecture`. -/
def OppermannConjecture : Prop :=
    ∀ (x : ℕ) (hx : 2 ≤ x),
    (∃ p ∈ Ioo (x * (x - 1)) (x^2), p.Prime) ∧
    (∃ p ∈ Ioo (x^2) (x * (x + 1)), p.Prime)

/-- `Andrica.andrica_conjecture`. -/
def AndricaConjecture : Prop :=
    ∀ (n : ℕ),
    Real.sqrt ((n+1).nth Nat.Prime) - Real.sqrt (n.nth Nat.Prime) < 1

/-- `Brocard.brocard_conjecture`: at least four primes between `p_n²` and `p_{n+1}²`. -/
def BrocardConjecture : Prop :=
    ∀ (n : ℕ) (hn : 1 ≤ n),
    letI prev := n.nth Nat.Prime;
    letI next := (n+1).nth Nat.Prime;
    4 ≤ ((Ioo (prev^2) (next^2)).filter Nat.Prime).card

/-! ## The per-index statements (the same bodies) -/

/-- Legendre at `n`: a prime in `(n², (n+1)²)`. -/
def LegendreAt (n : ℕ) : Prop := ∃ p ∈ Set.Ioo (n ^ 2) ((n + 1) ^ 2), Nat.Prime p

/-- Oppermann at `x`: primes in `(x(x−1), x²)` and in `(x², x(x+1))`. -/
def OppermannAt (x : ℕ) : Prop :=
    (∃ p ∈ Ioo (x * (x - 1)) (x^2), p.Prime) ∧
    (∃ p ∈ Ioo (x^2) (x * (x + 1)), p.Prime)

/-- Andrica at `n`: `√p_{n+1} − √p_n < 1`. -/
def AndricaAt (n : ℕ) : Prop :=
    Real.sqrt ((n+1).nth Nat.Prime) - Real.sqrt (n.nth Nat.Prime) < 1

/-- Brocard at `n`: at least four primes in `(p_n², p_{n+1}²)`. -/
def BrocardAt (n : ℕ) : Prop :=
    letI prev := n.nth Nat.Prime;
    letI next := (n+1).nth Nat.Prime;
    4 ≤ ((Ioo (prev^2) (next^2)).filter Nat.Prime).card

theorem legendreConjecture_iff : LegendreConjecture ↔ ∀ n ≥ 1, LegendreAt n := Iff.rfl
theorem oppermannConjecture_iff : OppermannConjecture ↔ ∀ x, 2 ≤ x → OppermannAt x := Iff.rfl
theorem andricaConjecture_iff : AndricaConjecture ↔ ∀ n, AndricaAt n := Iff.rfl
theorem brocardConjecture_iff : BrocardConjecture ↔ ∀ n, 1 ≤ n → BrocardAt n := Iff.rfl

/-! ## Exceptional sets, over the same index ranges as the conjectures -/

open Classical in
/-- The `n ∈ [1, N]` with no prime in `(n², (n+1)²)`. -/
noncomputable def legendreExceptions (N : ℕ) : Finset ℕ :=
  (Icc 1 N).filter (fun n => ¬ LegendreAt n)

open Classical in
/-- The `x ∈ [2, N]` at which Oppermann's statement fails. -/
noncomputable def oppermannExceptions (N : ℕ) : Finset ℕ :=
  (Icc 2 N).filter (fun x => ¬ OppermannAt x)

open Classical in
/-- The `n ∈ [0, N]` with `√p_{n+1} − √p_n ≥ 1`. -/
noncomputable def andricaExceptions (N : ℕ) : Finset ℕ :=
  (range (N + 1)).filter (fun n => ¬ AndricaAt n)

open Classical in
/-- The `n ∈ [1, N]` with fewer than four primes in `(p_n², p_{n+1}²)`. -/
noncomputable def brocardExceptions (N : ℕ) : Finset ℕ :=
  (Icc 1 N).filter (fun n => ¬ BrocardAt n)

/-! ## Targets -/

/-- Legendre fails for `O(log³ N)` of the `n ≤ N`. -/
def LegendreExceptionBound : Prop :=
  (fun N : ℕ => ((legendreExceptions N).card : ℝ)) =O[atTop] fun N => Real.log N ^ 3

/-- Oppermann fails for `O(log³ N)` of the `x ≤ N`. -/
def OppermannExceptionBound : Prop :=
  (fun N : ℕ => ((oppermannExceptions N).card : ℝ)) =O[atTop] fun N => Real.log N ^ 3

/-- Andrica fails for `O(log³ N)` of the `n ≤ N`. -/
def AndricaExceptionBound : Prop :=
  (fun N : ℕ => ((andricaExceptions N).card : ℝ)) =O[atTop] fun N => Real.log N ^ 3

/-- Brocard fails for `O(log³ N)` of the `n ≤ N`. -/
def BrocardExceptionBound : Prop :=
  (fun N : ℕ => ((brocardExceptions N).card : ℝ)) =O[atTop] fun N => Real.log N ^ 3

end LegendreExceptions
