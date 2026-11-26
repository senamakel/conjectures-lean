import Implications.PrimeGaps.Erdos382

/-!
# Cramér's conjecture implies Erdős Problem 680 (i)

Erdős Problem 680 (i) asks whether, for all large `n`, some `k ≥ 1` has `p(n + k) > k² + 1`,
where `p(m)` is the least prime factor of `m`. Any prime-gap bound `p_{m+1} - p_m ≤ √p_m` for
large `m` settles it: take `n + k` to be the first prime after `n`. Then `k` is at most one prime
gap, `k ≤ √p_m ≤ √n`, so `k² + 1 ≤ n + 1 ≤ n + k = p(n + k)`, with equality only for `n = 1`.

We prove it from `SubpowerGaps` (at `ε = 1/2`), hence from Cramér's conjecture, its strict
numerical form and Firoozbakht's conjecture (all copied verbatim from formal-conjectures in
`Implications.PrimeGaps.Erdos382`).

The target is copied word for word from google-deepmind/formal-conjectures at commit `9097e2f`.
-/

open Filter

namespace Implications.PrimeGaps

namespace Erdos680

/-- The statement of formal-conjectures `FormalConjectures/ErdosProblems/680.lean`,
`Erdos680.erdos_680.parts.i` (commit `9097e2f`, `research open`), copied verbatim as a `Prop`.

Is it true that, for all sufficiently large $n$, there exists some $k$ such that
$$
p(n+k)>k^2+1,
$$
where $p(m)$ denotes the least prime factor of $m$? -/
def Erdos680PartI : Prop :=
    ∀ᶠ (n : ℕ) in .atTop, ∃ k ≠ 0, (n + k).minFac > k^2 + 1

end Erdos680

/-- **Sub-power prime gaps imply Erdős 680 (i).** -/
theorem erdos_680_i_of_subpowerGaps (h : SubpowerGaps) : Erdos680.Erdos680PartI := by
  obtain ⟨N, hN⟩ := eventually_atTop.1 (h (1 / 2) (by norm_num))
  filter_upwards [eventually_ge_atTop (Nat.nth Nat.Prime N + 2)] with n hn
  have hinf := _root_.Nat.infinite_setOfPred_prime
  -- `p_m ≤ n < p_{m+1}`
  obtain ⟨m, hm1, hm2⟩ : ∃ m, Nat.nth Nat.Prime m ≤ n ∧ n < Nat.nth Nat.Prime (m + 1) := by
    have hc : 0 < _root_.Nat.count Nat.Prime (n + 1) := by
      rw [_root_.Nat.lt_nth_iff_count_lt hinf]
      have := (_root_.Nat.prime_nth_prime N).two_le
      rw [_root_.Nat.nth_prime_zero_eq_two]; omega
    refine ⟨_root_.Nat.count Nat.Prime (n + 1) - 1, ?_, ?_⟩
    · have := _root_.Nat.nth_lt_of_lt_count (p := Nat.Prime) (n := n + 1)
        (k := _root_.Nat.count Nat.Prime (n + 1) - 1) (by omega)
      omega
    · have := _root_.Nat.le_nth_count (p := Nat.Prime) hinf (n + 1)
      rw [Nat.sub_add_cancel hc]
      omega
  have hNm : N ≤ m := by
    by_contra hc
    push Not at hc
    have : Nat.nth Nat.Prime (m + 1) ≤ Nat.nth Nat.Prime N :=
      (_root_.Nat.nth_le_nth hinf).2 (by omega)
    omega
  set q := Nat.nth Nat.Prime (m + 1) with hq
  set p := Nat.nth Nat.Prime m with hp
  have hqP : q.Prime := _root_.Nat.prime_nth_prime _
  refine ⟨q - n, by omega, ?_⟩
  rw [Nat.add_sub_cancel' hm2.le, hqP.minFac_eq]
  -- the gap bound at `ε = 1/2`, squared
  have hg := hN m hNm
  have hp0 : (0 : ℝ) ≤ p := by positivity
  rw [← Real.sqrt_eq_rpow] at hg
  have hg0 : (0 : ℝ) ≤ primeGap m := by positivity
  have hsq : ((primeGap m : ℝ)) ^ 2 ≤ p := by
    calc ((primeGap m : ℝ)) ^ 2 ≤ Real.sqrt p ^ 2 := pow_le_pow_left₀ hg0 hg 2
      _ = p := Real.sq_sqrt hp0
  have hsqN : primeGap m ^ 2 ≤ p := by exact_mod_cast hsq
  have hgap : q - n ≤ primeGap m := by unfold primeGap; omega
  have hk2 : (q - n) ^ 2 ≤ primeGap m ^ 2 := Nat.pow_le_pow_left hgap 2
  -- `k² ≤ p ≤ n`, and `k = 1` forces `k² = 1 < n`
  have hk1 : q - n = 1 ∨ 2 ≤ q - n := by omega
  rcases hk1 with h1 | h2
  · rw [h1]; omega
  · have : (q - n) ^ 2 + 1 < n + (q - n) := by omega
    omega

/-- **Cramér's conjecture implies Erdős 680 (i).** -/
theorem erdos_680_i_of_cramer (h : CramerConjecture.CramerConjecture) :
    Erdos680.Erdos680PartI :=
  erdos_680_i_of_subpowerGaps (subpowerGaps_of_cramer h)

/-- **The strict numerical Cramér inequality implies Erdős 680 (i).** -/
theorem erdos_680_i_of_strictBound (h : CramerConjecture.StrictBound) :
    Erdos680.Erdos680PartI :=
  erdos_680_i_of_cramer (cramer_of_strictBound h)

/-- **Firoozbakht's conjecture implies Erdős 680 (i).** -/
theorem erdos_680_i_of_firoozbakht (h : Firoozbakht.FiroozbakhtConjecture) :
    Erdos680.Erdos680PartI :=
  erdos_680_i_of_cramer (cramer_of_firoozbakht h)

end Implications.PrimeGaps
