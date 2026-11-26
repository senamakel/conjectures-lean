import Implications.Dickson.Consecutive
import Implications.Erdos142.Statement

/-!
# Erdős Problem 141, consecutive primes in arithmetic progression, from Dickson's conjecture

Source: `FormalConjectures/ErdosProblems/141.lean`, formal-conjectures `9097e2f`:
`Erdos141.erdos_141`, `erdos_141.variants.eleven`, `erdos_141.variants.infinite_three` and
`erdos_141.variants.infinite_general_case` (all research open). The conclusions below are
verbatim, and so are the definitions `Set.IsPrimeProgressionOfLength`,
`Set.IsAPAndPrimeProgressionOfLength` and `consecutivePrimeArithmeticProgressions` (namespace
`Erdos141` there, `Implications.Dickson.Erdos141` here). `Set.IsAPOfLength` and
`Set.IsAPOfLengthWith` (`FormalConjecturesForMathlib/Combinatorics/AP/Basic.lean`) are already
copied verbatim in `Implications.Erdos142.Statement` and are imported from there.

For every `k ≥ 1`, Dickson's conjecture gives infinitely many runs of `k` consecutive primes
`n, n + k!, …, n + (k - 1) k!` (`infinite_consecutive_ap_of_dickson`). Each run is an arithmetic
progression of length `k` and a progression of `k` consecutive primes, and different `n` give
different sets.
-/

namespace Implications.Dickson.Erdos141

/-- Source: `FormalConjectures/ErdosProblems/141.lean`, `Erdos141.Set.IsPrimeProgressionOfLength`,
formal-conjectures `9097e2f`, verbatim.

The predicate that a set `s` consists of `l` consecutive primes (possibly infinite).
This predicate does not assert a specific value for the first term.
-/
def Set.IsPrimeProgressionOfLength (s : Set ℕ) (l : ℕ∞) : Prop :=
    ∃ a, ENat.card s = l ∧ s = {(a + n).nth Nat.Prime | (n : ℕ) (_ : n < l)}

open Nat Implications.Dickson.Erdos141

/-- Source: `FormalConjectures/ErdosProblems/141.lean`,
`Erdos141.Set.IsAPAndPrimeProgressionOfLength`, formal-conjectures `9097e2f`, verbatim.

The predicate that a set `s` is both an arithmetic progression of length `l` and a progression
of `l` consecutive primes.
-/
def Set.IsAPAndPrimeProgressionOfLength (s : Set ℕ) (l : ℕ) :=
   s.IsAPOfLength l ∧ s.IsPrimeProgressionOfLength l

/-- Source: `FormalConjectures/ErdosProblems/141.lean`,
`Erdos141.consecutivePrimeArithmeticProgressions`, formal-conjectures `9097e2f`, verbatim.

The set of arithmetic progressions of consecutive primes of length $k$.
-/
def consecutivePrimeArithmeticProgressions (k : ℕ) : Set (Set ℕ) :=
  {s | s.IsAPAndPrimeProgressionOfLength k}

theorem ap_set_eq (n d k : ℕ) :
    {n + i • d | (i : ℕ) (_ : i < (k : ℕ∞))} = ↑((Finset.range k).image fun i => n + i * d) := by
  ext x
  simp [smul_eq_mul]

theorem encard_ap_set (n d k : ℕ) (hd : 0 < d) :
    ENat.card {n + i • d | (i : ℕ) (_ : i < (k : ℕ∞))} = k := by
  rw [ap_set_eq, ENat.card_coe_set_eq, Set.encard_coe_eq_coe_finsetCard,
    Finset.card_image_of_injective, Finset.card_range]
  intro i j hij
  simp only [add_right_inj] at hij
  exact Nat.eq_of_mul_eq_mul_right hd hij

/-- Under Dickson's conjecture, for every `k ≥ 1`, the set of progressions of `k` consecutive
primes in arithmetic progression is infinite. -/
theorem infinite_consecutivePrimeArithmeticProgressions (hD : DicksonConjecture) (k : ℕ)
    (hk : 0 < k) : (consecutivePrimeArithmeticProgressions k).Infinite := by
  set d := k.factorial
  have hd : 0 < d := Nat.factorial_pos k
  let S : ℕ → Set ℕ := fun n => {n + i • d | (i : ℕ) (_ : i < (k : ℕ∞))}
  have hmem : ∀ n, n ∈ S n := fun n => ⟨0, by exact_mod_cast hk, by simp⟩
  have hge : ∀ n x, x ∈ S n → n ≤ x := by
    rintro n x ⟨i, -, rfl⟩
    exact Nat.le_add_right _ _
  have hinj : Set.InjOn S {n : ℕ | n.Prime ∧ ∀ i < k,
      Nat.nth Nat.Prime (Nat.count Nat.Prime n + i) = n + i * k.factorial} := by
    intro m _ n _ hmn
    have h1 := hge n m (hmn ▸ hmem m)
    have h2 := hge m n (hmn ▸ hmem n)
    omega
  refine ((infinite_consecutive_ap_of_dickson hD k hk).image hinj).mono ?_
  rintro _ ⟨n, ⟨hn, hap⟩, rfl⟩
  refine ⟨⟨n, d, encard_ap_set n d k hd, rfl⟩, ⟨Nat.count Nat.Prime n, encard_ap_set n d k hd, ?_⟩⟩
  ext x
  constructor
  · rintro ⟨i, hi, rfl⟩
    refine ⟨i, hi, ?_⟩
    rw [hap i (by exact_mod_cast hi), smul_eq_mul]
  · rintro ⟨i, hi, rfl⟩
    refine ⟨i, hi, ?_⟩
    rw [hap i (by exact_mod_cast hi), smul_eq_mul]

/-- Source: `FormalConjectures/ErdosProblems/141.lean`, `Erdos141.erdos_141`,
formal-conjectures `9097e2f` (research open); conclusion verbatim, under Dickson's conjecture. -/
theorem erdos_141_of_dickson (hD : DicksonConjecture) :
    ∀ k ≥ 3, ∃ (s : Set ℕ), s.IsAPAndPrimeProgressionOfLength k := by
  intro k hk
  exact (infinite_consecutivePrimeArithmeticProgressions hD k (by omega)).nonempty

/-- Source: `FormalConjectures/ErdosProblems/141.lean`, `Erdos141.erdos_141.variants.eleven`,
formal-conjectures `9097e2f` (research open); conclusion verbatim, under Dickson's conjecture. -/
theorem erdos_141_eleven_of_dickson (hD : DicksonConjecture) :
    ∃ (s : Set ℕ), s.IsAPAndPrimeProgressionOfLength 11 :=
  erdos_141_of_dickson hD 11 (by norm_num)

/-- Source: `FormalConjectures/ErdosProblems/141.lean`,
`Erdos141.erdos_141.variants.infinite_three`, formal-conjectures `9097e2f` (research open);
conclusion verbatim, under Dickson's conjecture. -/
theorem erdos_141_infinite_three_of_dickson (hD : DicksonConjecture) :
    (consecutivePrimeArithmeticProgressions 3).Infinite :=
  infinite_consecutivePrimeArithmeticProgressions hD 3 (by norm_num)

/-- Source: `FormalConjectures/ErdosProblems/141.lean`,
`Erdos141.erdos_141.variants.infinite_general_case`, formal-conjectures `9097e2f`
(research open); conclusion verbatim, under Dickson's conjecture. -/
theorem erdos_141_infinite_general_case_of_dickson (hD : DicksonConjecture) :
    ∀ k ≥ 3, (consecutivePrimeArithmeticProgressions k).Infinite :=
  fun k hk => infinite_consecutivePrimeArithmeticProgressions hD k (by omega)

end Implications.Dickson.Erdos141
