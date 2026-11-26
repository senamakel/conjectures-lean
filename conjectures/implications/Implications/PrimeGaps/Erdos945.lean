import Implications.PrimeGaps.Erdos382

/-!
# Cramér's conjecture implies Erdős Problem 945

Erdős Problem 945 asks whether `F(x) ≤ (log x)^{O(1)}`, where `F(x)` is the longest run of
consecutive integers `n + 1, …, n + k ≤ x` with pairwise distinct divisor counts `τ`, and in its
constant form whether every interval `[x, x + (log x)^C]` contains two integers with the same `τ`.
Two primes have `τ = 2`, so both follow from any gap bound `p_{m+1} - p_m ≤ A (log p_m)²`: two
consecutive gaps fit in a window of length `O((log x)²)`. This is the observation the
formal-conjectures file leaves as a TODO ("add observations what follows from Cramér's
conjecture"); it is attributed to Cambie in the atlas notes (unverified).

1. `exists_gap_le_of_cramer`: Cramér's conjecture gives `A > 0` with
   `p_{m+1} - p_m ≤ A (log p_m)²` for **every** `m` (the finitely many early gaps are absorbed
   into `A`, since `log p_m ≥ log 2 > 0`).
2. `erdos_945_constant_of_cramer`: two consecutive primes after `⌊x⌋` lie in
   `[x, x + 5 A (log x)²] ⊆ [x, x + (log x)³]` for large `x` (`C = 3`).
3. `erdos_945_of_cramer`: a window `(n, n + k]` with `n + k ≤ x` and injective `τ` holds at most
   one prime, so `k ≤ max 2 (2 A (log x)²) ≤ (log x)³` for large `x` (`O = 3`).

The definitions and both targets are copied word for word from google-deepmind/formal-conjectures
at commit `9097e2f`.
-/

open Filter Real

namespace Implications.PrimeGaps

namespace Erdos945

/-- Copied verbatim from formal-conjectures `FormalConjectures/ErdosProblems/945.lean`,
`Erdos945.τ` (commit `9097e2f`). -/
abbrev τ  := fun (n : ℕ) => n.divisors.card

/-- Copied verbatim from formal-conjectures `FormalConjectures/ErdosProblems/945.lean`,
`Erdos945.F` (commit `9097e2f`).

Let $F(x)$ be the maximal $k$ such that there exist $n+1, \dots, n+k \le x$
with $τ(n+1), \dots, τ(n+k)$ all distinct, where $τ(m)$ counts the divisors of $m$. -/
noncomputable def F (x : ℝ) : ℕ :=
  sSup {k | ∃ (n : ℕ), n + k ≤ x ∧ (Set.Ioc n (n + k)).InjOn τ}

/-- Copied verbatim from formal-conjectures `FormalConjectures/ErdosProblems/945.lean`,
`Erdos945.Erdos945Prop` (commit `9097e2f`); it is the statement of `Erdos945.erdos_945`
(`research open`).

Is it true that $F(x) \leq (\log x)^{O(1)}$? -/
def Erdos945Prop : Prop := ∃ O : ℝ → ℝ, O =O[atTop] (1 : ℝ → ℝ) ∧ ∀ᶠ x in atTop, F x ≤ log x ^ O x

/-- Copied verbatim from formal-conjectures `FormalConjectures/ErdosProblems/945.lean`,
`Erdos945.Erdos945Constant` (commit `9097e2f`); it is the statement of
`Erdos945.erdos_945.variants.constant` (`research open`).

Is there a constant $C > 0$ such that, for all large $x$, every interval $[x, x+(\log x)C]$
contains two integers with the same number of divisors? -/
def Erdos945Constant : Prop :=
  ∃ C > (0 : ℝ),  ∀ᶠ x : ℝ in atTop,
    ∃ a b : ℕ, a ≠ b ∧
    ↑a ∈ Set.Icc x (x + log x ^ C) ∧
    ↑b ∈ Set.Icc x (x + log x ^ C) ∧
    τ a = τ b

lemma τ_prime {p : ℕ} (hp : p.Prime) : τ p = 2 := by
  simp [τ, hp.divisors, Finset.card_pair hp.one_lt.ne]

end Erdos945

/-! ## A uniform gap bound from Cramér's conjecture -/

/-- **Cramér's conjecture, uniformly**: some `A > 0` has `p_{m+1} - p_m ≤ A (log p_m)²` for every
`m`. -/
theorem exists_gap_le_of_cramer (h : CramerConjecture.CramerConjecture) :
    ∃ A > (0 : ℝ), ∀ m : ℕ, (primeGap m : ℝ) ≤ A * Real.log (Nat.nth Nat.Prime m) ^ 2 := by
  obtain ⟨C, hC⟩ := h.bound
  obtain ⟨M, hM⟩ := eventually_atTop.1 hC
  have hl2 : 0 < Real.log 2 ^ 2 := by have := Real.log_pos one_lt_two; positivity
  set D : ℝ := ∑ i ∈ Finset.range M, (primeGap i : ℝ) with hD
  refine ⟨max C 0 + D / Real.log 2 ^ 2 + 1, by positivity, fun m ↦ ?_⟩
  have hp2 : (2 : ℝ) ≤ Nat.nth Nat.Prime m := by
    exact_mod_cast (_root_.Nat.prime_nth_prime m).two_le
  have hL2 : Real.log 2 ^ 2 ≤ Real.log (Nat.nth Nat.Prime m) ^ 2 :=
    pow_le_pow_left₀ (Real.log_nonneg one_le_two) (Real.log_le_log two_pos hp2) 2
  have hL0 : 0 ≤ Real.log (Nat.nth Nat.Prime m) ^ 2 := by positivity
  have hD0 : 0 ≤ D := by positivity
  rcases lt_or_ge m M with hm | hm
  · have h1 : (primeGap m : ℝ) ≤ D :=
      Finset.single_le_sum (f := fun i ↦ (primeGap i : ℝ)) (fun _ _ ↦ by positivity)
        (Finset.mem_range.2 hm)
    have h2 : D ≤ D / Real.log 2 ^ 2 * Real.log (Nat.nth Nat.Prime m) ^ 2 := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hl2]
      exact mul_le_mul_of_nonneg_left hL2 hD0
    have h3 : 0 ≤ (max C 0 + 1) * Real.log (Nat.nth Nat.Prime m) ^ 2 := by positivity
    nlinarith
  · have := hM m hm
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by positivity),
      abs_of_nonneg hL0] at this
    have h4 : C * Real.log (Nat.nth Nat.Prime m) ^ 2 ≤
        max C 0 * Real.log (Nat.nth Nat.Prime m) ^ 2 :=
      mul_le_mul_of_nonneg_right (le_max_left _ _) hL0
    have h5 : 0 ≤ (D / Real.log 2 ^ 2 + 1) * Real.log (Nat.nth Nat.Prime m) ^ 2 := by
      positivity
    nlinarith

/-- With a uniform gap bound `A`, every `m ≥ 2` has a prime `q` with `m < q ≤ m + A (log m)²`. -/
lemma exists_prime_lt_le {A : ℝ} (hA : 0 ≤ A)
    (hgap : ∀ m : ℕ, (primeGap m : ℝ) ≤ A * Real.log (Nat.nth Nat.Prime m) ^ 2)
    {m : ℕ} (hm : 2 ≤ m) :
    ∃ q : ℕ, q.Prime ∧ m < q ∧ (q : ℝ) ≤ m + A * Real.log m ^ 2 := by
  have hinf := _root_.Nat.infinite_setOfPred_prime
  obtain ⟨i, hi1, hi2⟩ : ∃ i, Nat.nth Nat.Prime i ≤ m ∧ m < Nat.nth Nat.Prime (i + 1) := by
    have hc : 0 < _root_.Nat.count Nat.Prime (m + 1) := by
      rw [_root_.Nat.lt_nth_iff_count_lt hinf, _root_.Nat.nth_prime_zero_eq_two]; omega
    refine ⟨_root_.Nat.count Nat.Prime (m + 1) - 1, ?_, ?_⟩
    · have := _root_.Nat.nth_lt_of_lt_count (p := Nat.Prime) (n := m + 1)
        (k := _root_.Nat.count Nat.Prime (m + 1) - 1) (by omega)
      omega
    · have := _root_.Nat.le_nth_count (p := Nat.Prime) hinf (m + 1)
      rw [Nat.sub_add_cancel hc]
      omega
  refine ⟨_, _root_.Nat.prime_nth_prime (i + 1), hi2, ?_⟩
  have hg := hgap i
  rw [primeGap, Nat.cast_sub (_root_.Nat.nth_strictMono hinf (Nat.lt_succ_self i)).le] at hg
  have hp2 : (2 : ℝ) ≤ Nat.nth Nat.Prime i := by
    exact_mod_cast (_root_.Nat.prime_nth_prime i).two_le
  have hpm : (Nat.nth Nat.Prime i : ℝ) ≤ m := by exact_mod_cast hi1
  have hlog : Real.log (Nat.nth Nat.Prime i) ^ 2 ≤ Real.log m ^ 2 :=
    pow_le_pow_left₀ (Real.log_nonneg (by linarith)) (Real.log_le_log (by linarith) hpm) 2
  nlinarith

/-! ## Headline theorems -/

/-- **Cramér's conjecture implies Erdős 945, constant form** (`C = 3`). -/
theorem erdos_945_constant_of_cramer (h : CramerConjecture.CramerConjecture) :
    Erdos945.Erdos945Constant := by
  obtain ⟨A, hA, hgap⟩ := exists_gap_le_of_cramer h
  refine ⟨3, by norm_num, ?_⟩
  -- `A (log x)² ≤ x` and `5 A ≤ log x` for large `x`
  have hlo : (fun x : ℝ => Real.log x ^ 2) =o[atTop] fun x => x := by
    simpa using isLittleO_log_rpow_rpow_atTop (2 : ℝ) one_pos
  filter_upwards [hlo.bound (inv_pos.2 hA), eventually_ge_atTop 2,
    Real.tendsto_log_atTop.eventually_ge_atTop (5 * A)] with x hx hx2 hlx
  have hx0 : 0 ≤ x := by linarith
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), abs_of_nonneg hx0] at hx
  have hAx : A * Real.log x ^ 2 ≤ x := by
    have := mul_le_mul_of_nonneg_left hx hA.le
    rwa [← mul_assoc, mul_inv_cancel₀ hA.ne', one_mul] at this
  set m := ⌊x⌋₊ with hm
  have hm1 : (m : ℝ) ≤ x := Nat.floor_le hx0
  have hm2 : x < m + 1 := Nat.lt_floor_add_one x
  have hm2' : 2 ≤ m := Nat.le_floor (by exact_mod_cast hx2)
  have hmR : (2 : ℝ) ≤ m := by exact_mod_cast hm2'
  have hlx0 : 0 ≤ Real.log x := Real.log_nonneg (by linarith)
  obtain ⟨q₁, hq₁, hmq₁, hq₁le⟩ := exists_prime_lt_le hA.le hgap hm2'
  obtain ⟨q₂, hq₂, hq₁₂, hq₂le⟩ := exists_prime_lt_le hA.le hgap (m := q₁) (by omega)
  have hlogm : Real.log m ^ 2 ≤ Real.log x ^ 2 :=
    pow_le_pow_left₀ (Real.log_nonneg (by linarith)) (Real.log_le_log (by linarith) hm1) 2
  have hq₁x : (q₁ : ℝ) ≤ x + A * Real.log x ^ 2 := by nlinarith
  -- `log q₁ ≤ log (2x) ≤ 2 log x`
  have hq₁R : (2 : ℝ) ≤ q₁ := by exact_mod_cast hq₁.two_le
  have hlq : Real.log q₁ ≤ 2 * Real.log x := by
    have h1 : (q₁ : ℝ) ≤ x ^ 2 := by nlinarith
    calc Real.log q₁ ≤ Real.log (x ^ 2) := Real.log_le_log (by linarith) h1
      _ = 2 * Real.log x := by rw [Real.log_pow]; norm_num
  have hlq2 : Real.log q₁ ^ 2 ≤ 4 * Real.log x ^ 2 := by
    have := pow_le_pow_left₀ (Real.log_nonneg (by linarith)) hlq 2
    nlinarith
  have hq₂x : (q₂ : ℝ) ≤ x + 5 * A * Real.log x ^ 2 := by nlinarith
  have hcube : 5 * A * Real.log x ^ 2 ≤ Real.log x ^ (3 : ℝ) := by
    rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    have : 0 ≤ Real.log x ^ 2 := sq_nonneg _
    nlinarith
  have hxq₁ : x ≤ q₁ := by
    have : (m : ℝ) + 1 ≤ q₁ := by exact_mod_cast hmq₁
    linarith
  have hq₁q₂ : (q₁ : ℝ) ≤ q₂ := by exact_mod_cast hq₁₂.le
  refine ⟨q₁, q₂, hq₁₂.ne, ⟨hxq₁, by linarith⟩, ⟨by linarith, by linarith⟩, ?_⟩
  rw [Erdos945.τ_prime hq₁, Erdos945.τ_prime hq₂]

/-- **Cramér's conjecture implies Erdős 945**: `F(x) ≤ (log x)³` for large `x`. -/
theorem erdos_945_of_cramer (h : CramerConjecture.CramerConjecture) : Erdos945.Erdos945Prop := by
  obtain ⟨A, hA, hgap⟩ := exists_gap_le_of_cramer h
  refine ⟨fun _ ↦ 3, ?_, ?_⟩
  · simpa [Pi.one_def] using Asymptotics.isBigO_const_const (3 : ℝ) (one_ne_zero (α := ℝ)) (atTop : Filter ℝ)
  filter_upwards [eventually_ge_atTop 2,
    Real.tendsto_log_atTop.eventually_ge_atTop (2 * A + 2)] with x hx2 hlx
  have hlx1 : 1 ≤ Real.log x := by linarith
  have hbound : (2 : ℝ) * A * Real.log x ^ 2 + 2 ≤ Real.log x ^ (3 : ℝ) := by
    rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    have : 1 ≤ Real.log x ^ 2 := one_le_pow₀ hlx1
    nlinarith
  -- every admissible `k` is at most `2 A (log x)² + 2`
  suffices hk : ∀ k ∈ {k : ℕ | ∃ (n : ℕ), n + k ≤ x ∧ (Set.Ioc n (n + k)).InjOn Erdos945.τ},
      (k : ℝ) ≤ 2 * A * Real.log x ^ 2 + 2 by
    have hF : (Erdos945.F x : ℝ) ≤ 2 * A * Real.log x ^ 2 + 2 := by
      have hne : (2 * A * Real.log x ^ 2 + 2) ≥ 0 := by positivity
      set B := ⌊2 * A * Real.log x ^ 2 + 2⌋₊
      have : Erdos945.F x ≤ B := csSup_le' fun k hk' ↦ Nat.le_floor (hk k hk')
      calc (Erdos945.F x : ℝ) ≤ B := by exact_mod_cast this
        _ ≤ _ := Nat.floor_le hne
    linarith
  rintro k ⟨n, hnk, hinj⟩
  -- two distinct primes in `(n, n + k]` contradict injectivity
  have two : ∀ q₁ q₂ : ℕ, q₁.Prime → q₂.Prime → q₁ ≠ q₂ → n < q₁ → q₁ ≤ n + k → n < q₂ →
      q₂ ≤ n + k → False := fun q₁ q₂ h1 h2 hne a1 a2 b1 b2 ↦
    hne (hinj ⟨a1, a2⟩ ⟨b1, b2⟩ (by rw [Erdos945.τ_prime h1, Erdos945.τ_prime h2]))
  have hnkR : (n : ℝ) + k ≤ x := hnk
  have hlog0 : 0 ≤ Real.log x ^ 2 := sq_nonneg _
  have hAL : 0 ≤ A * Real.log x ^ 2 := by positivity
  rcases lt_or_ge n 2 with hn | hn
  · -- `2, 3 ∈ (n, n + k]` once `k ≥ 3`
    by_contra hc
    push Not at hc
    have hk3 : 3 ≤ k := by
      have : (2 : ℝ) < k := by linarith
      have : 2 < k := by exact_mod_cast this
      omega
    exact two 2 3 Nat.prime_two Nat.prime_three (by norm_num) (by omega) (by omega)
      (by omega) (by omega)
  · have hnR : (n : ℝ) ≤ x := by
      have : (0 : ℝ) ≤ k := by positivity
      linarith
    have hlogle : ∀ y : ℕ, 2 ≤ y → (y : ℝ) ≤ x → Real.log y ^ 2 ≤ Real.log x ^ 2 := by
      intro y hy hyx
      have : (2 : ℝ) ≤ y := by exact_mod_cast hy
      exact pow_le_pow_left₀ (Real.log_nonneg (by linarith)) (Real.log_le_log (by linarith) hyx) 2
    obtain ⟨q₁, hq₁, hnq₁, hq₁le⟩ := exists_prime_lt_le hA.le hgap hn
    have hq₁le' : (q₁ : ℝ) ≤ n + A * Real.log x ^ 2 := by
      have := hlogle n hn hnR
      nlinarith
    rcases lt_or_ge (n + k) q₁ with hc | hc
    · have : ((n + k : ℕ) : ℝ) < q₁ := by exact_mod_cast hc
      push_cast at this
      nlinarith
    · obtain ⟨q₂, hq₂, hq₁₂, hq₂le⟩ := exists_prime_lt_le hA.le hgap (m := q₁) hq₁.two_le
      have hq₁x : (q₁ : ℝ) ≤ x := by
        have : (q₁ : ℝ) ≤ ((n + k : ℕ) : ℝ) := by exact_mod_cast hc
        push_cast at this; linarith
      have hq₂le' : (q₂ : ℝ) ≤ q₁ + A * Real.log x ^ 2 := by
        have := hlogle q₁ hq₁.two_le hq₁x
        nlinarith
      rcases lt_or_ge (n + k) q₂ with hc2 | hc2
      · have : ((n + k : ℕ) : ℝ) < q₂ := by exact_mod_cast hc2
        push_cast at this
        nlinarith
      · exact (two q₁ q₂ hq₁ hq₂ hq₁₂.ne hnq₁ hc (by omega) hc2).elim

end Implications.PrimeGaps
