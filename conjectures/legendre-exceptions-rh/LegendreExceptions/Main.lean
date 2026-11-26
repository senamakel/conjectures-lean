import LegendreExceptions.Core

/-!
# The four exceptional-set bounds under RH

Each failure of the per-index statement gives a prime-free interval `(a, b)` with `m ≤ a`,
`√a ≤ 2 (b − a)` and `a < (N + 2)^8` for `m ≤ N`; failures at distinct indices give disjoint
intervals. `isBigO_of_RH` (`Core.lean`) then gives `O(log³ N)`.

* Legendre at `n`: the interval `(n², (n+1)²)`, length `2n + 1`.
* Oppermann at `x`: `(x(x−1), x²)` or `(x², x(x+1))`, whichever has no prime; length `x`.
  These intervals tile `ℕ`, so distinct `x` give disjoint intervals.
* Andrica at `n`: the gap `(p_n, p_{n+1})`, of length `≥ 2√p_n + 1`.
* Brocard at `n` (`p = p_n`): one of `(p², p(p+1))`, `(p(p+1), (p+1)²)`, `((p+1)², (p+1)(p+2))`,
  `((p+1)(p+2), (p+2)²)` has no prime, otherwise these four primes lie in `(p², p_{n+1}²)`
  because `p_{n+1} ≥ p + 2`. Length `≥ p`.

The bound `p_n ≤ (n + 2)³` (`nth_prime_le_cube`) comes from Bertrand's postulate for `n ≤ 4`
and from Mathlib's Chebyshev bound `π(m) ≥ m log 2 / log m` (at `m = n³`) for `n ≥ 5`.
-/

namespace LegendreExceptions

open Finset Real Nat Erdos233

/-! ## Elementary facts about `p_n` -/

lemma nth_prime_le_two_pow (n : ℕ) : nth Nat.Prime n ≤ 2 ^ (n + 1) := by
  induction n with
  | zero => rw [Nat.nth_prime_zero_eq_two]; norm_num
  | succ k ih =>
    have := nth_succ_le_two_mul k
    rw [pow_succ]; omega

/-- `p_n ≤ (n + 2)³`. -/
lemma nth_prime_le_cube (n : ℕ) : nth Nat.Prime n ≤ (n + 2) ^ 3 := by
  rcases Nat.lt_or_ge n 5 with hn | hn
  · refine (nth_prime_le_two_pow n).trans ?_
    interval_cases n <;> norm_num
  · have hm : 4 ≤ n ^ 3 := le_trans (by norm_num) (Nat.pow_le_pow_left hn 3)
    have hpi := Chebyshev.pi_ge_of_four_le hm
    have hn5 : (5 : ℝ) ≤ n := by exact_mod_cast hn
    have hlogn : 0 < Real.log n := Real.log_pos (by linarith)
    have hlogle : Real.log n ≤ n - 1 := Real.log_le_sub_one_of_pos (by linarith)
    have hl2 := Real.log_two_gt_d9
    have hlog3 : Real.log ((n ^ 3 : ℕ) : ℝ) = 3 * Real.log n := by
      push_cast; rw [Real.log_pow]; norm_num
    rw [hlog3] at hpi
    have hlt : (n : ℝ) < (n ^ 3 : ℕ) * Real.log 2 / (3 * Real.log n) := by
      rw [lt_div_iff₀ (by positivity)]
      push_cast
      have : 3 * ((n : ℝ) - 1) < (n : ℝ) ^ 2 * Real.log 2 := by nlinarith
      have h1 : (n : ℝ) * (3 * Real.log n) ≤ n * (3 * ((n : ℝ) - 1)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity); linarith
      nlinarith
    have hcount : n < Nat.count Nat.Prime (n ^ 3 + 1) := by
      have : (n : ℝ) < (Nat.primeCounting (n ^ 3) : ℝ) := lt_of_lt_of_le hlt hpi
      exact_mod_cast this
    have := Nat.nth_lt_of_lt_count hcount
    have : n ^ 3 ≤ (n + 2) ^ 3 := Nat.pow_le_pow_left (by omega) 3
    omega

lemma three_le_nth_prime {n : ℕ} (hn : 1 ≤ n) : 3 ≤ nth Nat.Prime n :=
  Nat.nth_prime_one_eq_three ▸ (Nat.nth_le_nth Nat.infinite_setOfPred_prime).2 hn

/-- `p_{n+1} ≥ p_n + 2` for `n ≥ 1`. -/
lemma nth_prime_add_two_le {n : ℕ} (hn : 1 ≤ n) :
    nth Nat.Prime n + 2 ≤ nth Nat.Prime (n + 1) := by
  have h3 := three_le_nth_prime hn
  have h3' := three_le_nth_prime (n := n + 1) (by omega)
  have hlt : nth Nat.Prime n < nth Nat.Prime (n + 1) :=
    Nat.nth_strictMono Nat.infinite_setOfPred_prime (Nat.lt_succ_self n)
  rcases (Nat.prime_nth_prime n).eq_two_or_odd' with h | ⟨k, hk⟩
  · omega
  rcases (Nat.prime_nth_prime (n + 1)).eq_two_or_odd' with h | ⟨m, hm⟩
  · omega
  omega

lemma sq_lt_bound {m N : ℕ} (hm : m ≤ N) : m ^ 2 < (N + 2) ^ 8 := by
  calc m ^ 2 < (N + 2) ^ 2 := Nat.pow_lt_pow_left (by omega) two_ne_zero
    _ ≤ (N + 2) ^ 8 := Nat.pow_le_pow_right (by omega) (by norm_num)

/-! ## Legendre -/

/-- **Legendre's exceptional set under RH**: for all but `O(log³ N)` of the `n ≤ N` there is a
prime between `n²` and `(n+1)²`. -/
theorem legendre_exceptions_of_RH (hRH : RiemannHypothesis) : LegendreExceptionBound := by
  refine isBigO_of_RH hRH (fun m => 1 ≤ m ∧ ¬ LegendreAt m) (fun m => m ^ 2)
    (fun m => (m + 1) ^ 2) ?_ ?_ legendreExceptions ?_
  · rintro m ⟨-, hm⟩
    refine ⟨Nat.le_self_pow two_ne_zero m, ?_, ?_⟩
    · push_cast
      rw [Real.sqrt_sq (by positivity)]
      nlinarith
    · intro y h1 h2 hy
      exact hm ⟨y, ⟨h1, h2⟩, hy⟩
  · rintro m n - - hne
    rw [Finset.disjoint_left]
    intro y hy1 hy2
    rw [mem_Ioo] at hy1 hy2
    rcases Nat.lt_or_gt_of_ne hne with h | h
    · have : (m + 1) ^ 2 ≤ n ^ 2 := Nat.pow_le_pow_left h 2
      omega
    · have : (n + 1) ^ 2 ≤ m ^ 2 := Nat.pow_le_pow_left h 2
      omega
  · intro N m hm
    simp only [legendreExceptions, mem_filter, mem_Icc] at hm
    exact ⟨⟨hm.1.1, hm.2⟩, sq_lt_bound hm.1.2⟩

/-! ## Oppermann -/

/-- `(l, r)` contains a prime. -/
def HasPrime (l r : ℕ) : Prop := ∃ p ∈ Ioo l r, p.Prime

instance (l r : ℕ) : Decidable (HasPrime l r) := by unfold HasPrime; infer_instance

/-- Left end of a prime-free Oppermann interval at `x`. -/
def oppA (x : ℕ) : ℕ := if HasPrime (x * (x - 1)) (x ^ 2) then x ^ 2 else x * (x - 1)

/-- Right end of a prime-free Oppermann interval at `x`. -/
def oppB (x : ℕ) : ℕ := if HasPrime (x * (x - 1)) (x ^ 2) then x * (x + 1) else x ^ 2

lemma opp_bounds (x : ℕ) : x * (x - 1) ≤ oppA x ∧ oppB x ≤ x * (x + 1) ∧ oppA x ≤ x ^ 2 ∧
    oppA x + x = oppB x := by
  obtain ⟨k, rfl⟩ | rfl : (∃ k, x = k + 1) ∨ x = 0 := by
    rcases x with _ | k
    · exact Or.inr rfl
    · exact Or.inl ⟨k, rfl⟩
  · simp only [Nat.add_sub_cancel]
    unfold oppA oppB
    simp only [Nat.add_sub_cancel]
    split_ifs <;> refine ⟨?_, ?_, ?_, ?_⟩ <;> ring_nf <;> nlinarith
  · simp [oppA, oppB]

/-- **Oppermann's exceptional set under RH**: for all but `O(log³ N)` of the `x ≤ N` there are
primes in `(x(x−1), x²)` and in `(x², x(x+1))`. -/
theorem oppermann_exceptions_of_RH (hRH : RiemannHypothesis) : OppermannExceptionBound := by
  refine isBigO_of_RH hRH (fun x => 2 ≤ x ∧ ¬ OppermannAt x) oppA oppB ?_ ?_
    oppermannExceptions ?_
  · rintro x ⟨hx, hO⟩
    obtain ⟨h1, h2, h3, h4⟩ := opp_bounds x
    refine ⟨?_, ?_, ?_⟩
    · have : x ≤ x * (x - 1) := Nat.le_mul_of_pos_right x (by omega)
      omega
    · have e : (oppB x : ℝ) - oppA x = x := by
        rw [← h4]; push_cast; ring
      rw [e]
      have : Real.sqrt (oppA x) ≤ x := by
        rw [Real.sqrt_le_left (by positivity)]
        exact_mod_cast h3
      linarith
    · intro y hy1 hy2 hy
      unfold oppA oppB at *
      split_ifs at hy1 hy2 with hP
      · exact hO ⟨hP, ⟨y, mem_Ioo.2 ⟨hy1, hy2⟩, hy⟩⟩
      · exact hP ⟨y, mem_Ioo.2 ⟨hy1, hy2⟩, hy⟩
  · rintro x x' ⟨hx, -⟩ ⟨hx', -⟩ hne
    rw [Finset.disjoint_left]
    intro y hy1 hy2
    rw [mem_Ioo] at hy1 hy2
    obtain ⟨a1, a2, -, -⟩ := opp_bounds x
    obtain ⟨b1, b2, -, -⟩ := opp_bounds x'
    rcases Nat.lt_or_gt_of_ne hne with h | h
    · have : x * (x + 1) ≤ x' * (x' - 1) := by
        rw [mul_comm x']; exact Nat.mul_le_mul (by omega) (by omega)
      omega
    · have : x' * (x' + 1) ≤ x * (x - 1) := by
        rw [mul_comm x]; exact Nat.mul_le_mul (by omega) (by omega)
      omega
  · intro N x hx
    simp only [oppermannExceptions, mem_filter, mem_Icc] at hx
    refine ⟨⟨hx.1.1, hx.2⟩, ?_⟩
    exact lt_of_le_of_lt (opp_bounds x).2.2.1 (sq_lt_bound hx.1.2)

/-! ## Andrica -/

/-- **Andrica's exceptional set under RH**: `√p_{n+1} − √p_n < 1` for all but `O(log³ N)` of
the `n ≤ N`. -/
theorem andrica_exceptions_of_RH (hRH : RiemannHypothesis) : AndricaExceptionBound := by
  refine isBigO_of_RH hRH (fun n => ¬ AndricaAt n) (fun n => nth Nat.Prime n)
    (fun n => nth Nat.Prime (n + 1)) ?_ ?_ andricaExceptions ?_
  · intro n hA
    refine ⟨by have := Nat.add_two_le_nth_prime n; omega, ?_, ?_⟩
    · unfold AndricaAt at hA
      push_neg at hA
      have hp : (0 : ℝ) ≤ nth Nat.Prime n := Nat.cast_nonneg _
      have hq : (0 : ℝ) ≤ nth Nat.Prime (n + 1) := Nat.cast_nonneg _
      have e1 := Real.sq_sqrt hp
      have e2 := Real.sq_sqrt hq
      have s1 := Real.sqrt_nonneg (nth Nat.Prime n : ℝ)
      nlinarith
    · intro y h1 h2
      exact not_prime_between h1 h2
  · rintro m n - - hne
    rw [Finset.disjoint_left]
    intro y hy1 hy2
    rw [mem_Ioo] at hy1 hy2
    rcases Nat.lt_or_gt_of_ne hne with h | h
    · have : nth Nat.Prime (m + 1) ≤ nth Nat.Prime n :=
        (Nat.nth_le_nth Nat.infinite_setOfPred_prime).2 (show m + 1 ≤ n by omega)
      omega
    · have : nth Nat.Prime (n + 1) ≤ nth Nat.Prime m :=
        (Nat.nth_le_nth Nat.infinite_setOfPred_prime).2 (show n + 1 ≤ m by omega)
      omega
  · intro N n hn
    simp only [andricaExceptions, mem_filter, mem_range] at hn
    refine ⟨hn.2, ?_⟩
    calc nth Nat.Prime n ≤ (n + 2) ^ 3 := nth_prime_le_cube n
      _ < (N + 2) ^ 8 := by
        calc (n + 2) ^ 3 ≤ (N + 2) ^ 3 := Nat.pow_le_pow_left (by omega) 3
          _ < (N + 2) ^ 8 := Nat.pow_lt_pow_right (by omega) (by norm_num)

/-! ## Brocard -/

/-- Left end of a prime-free quarter of `(p², (p+2)²)`, `p = p_n`. -/
noncomputable def broA (n : ℕ) : ℕ :=
  let p := nth Nat.Prime n
  if ¬ HasPrime (p ^ 2) (p * (p + 1)) then p ^ 2
  else if ¬ HasPrime (p * (p + 1)) ((p + 1) ^ 2) then p * (p + 1)
  else if ¬ HasPrime ((p + 1) ^ 2) ((p + 1) * (p + 2)) then (p + 1) ^ 2
  else (p + 1) * (p + 2)

/-- Right end of a prime-free quarter of `(p², (p+2)²)`, `p = p_n`. -/
noncomputable def broB (n : ℕ) : ℕ :=
  let p := nth Nat.Prime n
  if ¬ HasPrime (p ^ 2) (p * (p + 1)) then p * (p + 1)
  else if ¬ HasPrime (p * (p + 1)) ((p + 1) ^ 2) then (p + 1) ^ 2
  else if ¬ HasPrime ((p + 1) ^ 2) ((p + 1) * (p + 2)) then (p + 1) * (p + 2)
  else (p + 2) ^ 2

/-- Four primes in the four quarters of `(p², (p+2)²)` give Brocard at `n`. -/
lemma brocardAt_of_four {n : ℕ} (hn : 1 ≤ n)
    (h1 : HasPrime (nth Nat.Prime n ^ 2) (nth Nat.Prime n * (nth Nat.Prime n + 1)))
    (h2 : HasPrime (nth Nat.Prime n * (nth Nat.Prime n + 1)) ((nth Nat.Prime n + 1) ^ 2))
    (h3 : HasPrime ((nth Nat.Prime n + 1) ^ 2) ((nth Nat.Prime n + 1) * (nth Nat.Prime n + 2)))
    (h4 : HasPrime ((nth Nat.Prime n + 1) * (nth Nat.Prime n + 2)) ((nth Nat.Prime n + 2) ^ 2)) :
    BrocardAt n := by
  set p := nth Nat.Prime n with hp
  have hq := nth_prime_add_two_le hn
  rw [← hp] at hq
  set q := nth Nat.Prime (n + 1) with hqdef
  show 4 ≤ ((Ioo (p ^ 2) (q ^ 2)).filter Nat.Prime).card
  obtain ⟨r1, hr1, pr1⟩ := h1
  obtain ⟨r2, hr2, pr2⟩ := h2
  obtain ⟨r3, hr3, pr3⟩ := h3
  obtain ⟨r4, hr4, pr4⟩ := h4
  rw [mem_Ioo] at hr1 hr2 hr3 hr4
  have hsq : (p + 2) ^ 2 ≤ q ^ 2 := Nat.pow_le_pow_left hq 2
  have e1 : p * (p + 1) = p ^ 2 + p := by ring
  have e2 : (p + 1) ^ 2 = p ^ 2 + 2 * p + 1 := by ring
  have e3 : (p + 1) * (p + 2) = p ^ 2 + 3 * p + 2 := by ring
  have e4 : (p + 2) ^ 2 = p ^ 2 + 4 * p + 4 := by ring
  rw [e1, e2] at hr2
  rw [e1] at hr1
  rw [e2, e3] at hr3
  rw [e3, e4] at hr4
  rw [e4] at hsq
  have hsub : ({r1, r2, r3, r4} : Finset ℕ) ⊆ (Ioo (p ^ 2) (q ^ 2)).filter Nat.Prime := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rw [mem_filter, mem_Ioo]
    rcases hx with rfl | rfl | rfl | rfl
    · exact ⟨⟨by omega, by omega⟩, pr1⟩
    · exact ⟨⟨by omega, by omega⟩, pr2⟩
    · exact ⟨⟨by omega, by omega⟩, pr3⟩
    · exact ⟨⟨by omega, by omega⟩, pr4⟩
  have hcard : ({r1, r2, r3, r4} : Finset ℕ).card = 4 := by
    rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_pair]
    · omega
    · simp only [Finset.mem_insert, Finset.mem_singleton]; omega
    · simp only [Finset.mem_insert, Finset.mem_singleton]; omega
  exact hcard ▸ card_le_card hsub

lemma broA_broB (n : ℕ) :
    nth Nat.Prime n ^ 2 ≤ broA n ∧ broA n ≤ (nth Nat.Prime n + 1) * (nth Nat.Prime n + 2) ∧
      broA n + nth Nat.Prime n ≤ broB n ∧ broB n ≤ (nth Nat.Prime n + 2) ^ 2 := by
  unfold broA broB
  dsimp only
  split_ifs <;> refine ⟨?_, ?_, ?_, ?_⟩ <;> ring_nf <;> nlinarith

/-- **Brocard's exceptional set under RH**: for all but `O(log³ N)` of the `n ≤ N` there are at
least four primes between `p_n²` and `p_{n+1}²`. -/
theorem brocard_exceptions_of_RH (hRH : RiemannHypothesis) : BrocardExceptionBound := by
  refine isBigO_of_RH hRH (fun n => 1 ≤ n ∧ ¬ BrocardAt n) broA broB ?_ ?_
    brocardExceptions ?_
  · rintro n ⟨hn, hB⟩
    obtain ⟨a1, a2, a3, a4⟩ := broA_broB n
    set p := nth Nat.Prime n with hp
    have hp3 : 3 ≤ p := three_le_nth_prime hn
    refine ⟨?_, ?_, ?_⟩
    · have := Nat.add_two_le_nth_prime n
      have : p ≤ p ^ 2 := Nat.le_self_pow two_ne_zero p
      omega
    · have hb : (broA n : ℝ) + p ≤ broB n := by exact_mod_cast a3
      have ha : (broA n : ℝ) ≤ (p + 2) ^ 2 := by
        have : broA n ≤ (p + 2) ^ 2 := le_trans a2 (by nlinarith)
        exact_mod_cast this
      have hs : Real.sqrt (broA n) ≤ p + 2 := by
        rw [Real.sqrt_le_left (by positivity)]; exact ha
      have : (3 : ℝ) ≤ p := by exact_mod_cast hp3
      linarith
    · intro y hy1 hy2 hy
      have hP : ∀ l r, ¬ HasPrime l r → l < y → y < r → False :=
        fun l r h h1 h2 => h ⟨y, mem_Ioo.2 ⟨h1, h2⟩, hy⟩
      unfold broA at hy1
      unfold broB at hy2
      dsimp only at hy1 hy2
      split_ifs at hy1 hy2 <;> first
        | (refine hP _ _ ?_ hy1 hy2; assumption)
        | exact hB (brocardAt_of_four hn (by assumption) (by assumption) (by assumption)
            ⟨y, mem_Ioo.2 ⟨hy1, hy2⟩, hy⟩)
  · rintro m n ⟨hm, -⟩ ⟨hn, -⟩ hne
    rw [Finset.disjoint_left]
    intro y hy1 hy2
    rw [mem_Ioo] at hy1 hy2
    obtain ⟨a1, -, -, a4⟩ := broA_broB m
    obtain ⟨b1, -, -, b4⟩ := broA_broB n
    rcases Nat.lt_or_gt_of_ne hne with h | h
    · have h1 := nth_prime_add_two_le hm
      have h2 : nth Nat.Prime (m + 1) ≤ nth Nat.Prime n :=
        (Nat.nth_le_nth Nat.infinite_setOfPred_prime).2 (show m + 1 ≤ n by omega)
      have : (nth Nat.Prime m + 2) ^ 2 ≤ nth Nat.Prime n ^ 2 := Nat.pow_le_pow_left (by omega) 2
      omega
    · have h1 := nth_prime_add_two_le hn
      have h2 : nth Nat.Prime (n + 1) ≤ nth Nat.Prime m :=
        (Nat.nth_le_nth Nat.infinite_setOfPred_prime).2 (show n + 1 ≤ m by omega)
      have : (nth Nat.Prime n + 2) ^ 2 ≤ nth Nat.Prime m ^ 2 := Nat.pow_le_pow_left (by omega) 2
      omega
  · intro N n hn
    simp only [brocardExceptions, mem_filter, mem_Icc] at hn
    refine ⟨⟨hn.1.1, hn.2⟩, ?_⟩
    obtain ⟨-, a2, -, -⟩ := broA_broB n
    set p := nth Nat.Prime n with hp
    have hc : p ≤ (n + 2) ^ 3 := nth_prime_le_cube n
    have h1 : p + 2 ≤ (N + 2) ^ 4 := by
      have : (n + 2) ^ 3 ≤ (N + 2) ^ 3 := Nat.pow_le_pow_left (by omega) 3
      have : (N + 2) ^ 4 = (N + 2) ^ 3 * (N + 2) := by ring
      have : 2 ≤ (N + 2) ^ 3 :=
        le_trans (by norm_num) (Nat.pow_le_pow_left (show 2 ≤ N + 2 by omega) 3)
      have : (N + 2) ^ 3 * 2 ≤ (N + 2) ^ 3 * (N + 2) := Nat.mul_le_mul_left _ (by omega)
      omega
    calc broA n ≤ (p + 1) * (p + 2) := a2
      _ < (p + 2) ^ 2 := by nlinarith
      _ ≤ ((N + 2) ^ 4) ^ 2 := Nat.pow_le_pow_left h1 2
      _ = (N + 2) ^ 8 := by ring

end LegendreExceptions
