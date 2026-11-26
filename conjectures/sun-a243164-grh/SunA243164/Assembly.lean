import SunA243164.Statement

/-!
# Assembly: the statement from a per-prime property

The statement is indexed by `n`; everything else is indexed by the prime `P = p_n`, with
`n = π(P)`. `GoodPrime P` says that some prime `q < π(P)` has `q · π(P)` a primitive root
modulo `P`. The theorem follows from `GoodPrime P` for every prime `P` with `π(P) > 6`, which
is split into an analytic part (`P ≥ N`) and a finite range (`P < N`).
-/

namespace SunA243164

/-- Some prime `q < π(P)` has `q · π(P)` a primitive root modulo `P`. -/
def GoodPrime (P : ℕ) : Prop :=
  ∃ q : ℕ, q.Prime ∧ q < Nat.primeCounting P ∧
    orderOf ((q * Nat.primeCounting P : ℕ) : ZMod P) = P - 1

/-- Every prime `P ≥ N` is good (the analytic part). -/
def GoodFrom (N : ℕ) : Prop := ∀ P : ℕ, P.Prime → N ≤ P → GoodPrime P

/-- Every prime `P < N` of index `π(P) > 6` is good (the finite range). -/
def VerifiedBelow (N : ℕ) : Prop :=
  ∀ P : ℕ, P.Prime → 6 < Nat.primeCounting P → P < N → GoodPrime P

/-- `π(p_n) = n` for `n ≥ 1`. -/
lemma primeCounting_nthPrime {n : ℕ} (hn : 1 ≤ n) :
    Nat.primeCounting (Nat.nth Nat.Prime (n - 1)) = n := by
  rw [Nat.primeCounting, Nat.primeCounting', Nat.count_succ,
    Nat.count_nth_of_infinite Nat.infinite_setOfPred_prime]
  simp [Nat.prime_nth_prime]; omega

/-- **Assembly.** The analytic part and the finite range give Sun's statement. -/
theorem sunA243164_of_goodFrom_of_verified {N : ℕ} (hA : GoodFrom N) (hV : VerifiedBelow N) :
    SunA243164Statement := by
  intro n hn
  set P := Nat.nth Nat.Prime (n - 1)
  have hP : P.Prime := Nat.prime_nth_prime _
  have hπ : Nat.primeCounting P = n := primeCounting_nthPrime (by omega)
  have hgood : GoodPrime P := by
    by_cases h : N ≤ P
    · exact hA P hP h
    · exact hV P hP (by omega) (by omega)
  obtain ⟨q, hq, hqn, hord⟩ := hgood
  rw [hπ] at hqn hord
  exact ⟨q, hq, hqn, hord⟩

end SunA243164
