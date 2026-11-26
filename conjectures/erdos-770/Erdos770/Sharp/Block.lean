import Erdos770.Core
import Erdos770.Sharp.Primes

/-!
# Block certificates

A block is a range `2^k ≤ n^q < 2^(k+1)`. Its certificate `(K', j, m, p)` passes `blockOK` when,
with `Ka = ⌈5 (k a / q)²⌉` (`a = 0.693147 < log 2`, so `Ka ≤ ⌈5 log² n⌉`):

* `17 ≤ Ka`, `K' ≤ Ka`, `K'^(j q) ≤ 2^m`;
* `(m b / q + 13/4)² ≤ Ka` with `b = 0.6931472 > log 2`;
* `2^(k+1) ≤ C(p, j)^q`;

and `p ≤ π(K')`. `block_false`: such a certificate rules out a bad prime `r` with
`M < (log r + 13/4)²` and `M ≥ ⌈5 log² n⌉`: then `m log 2 < q log r`, so `K'^j < r`, the products
of `j` primes `≤ K'` give `C(π K', j) ≤ n` (`choose_le_of_bad`), and `C(p, j)^q ≤ n^q < 2^(k+1)`.
-/

namespace Erdos770.Sharp

/-- `C(p, j)` by the product formula (the kernel evaluates it quickly). -/
def chooseB (p j : ℕ) : ℕ := p.descFactorial j / j.factorial

lemma chooseB_eq (p j : ℕ) : chooseB p j = p.choose j :=
  (Nat.choose_eq_descFactorial_div_factorial p j).symm

def blockOK (q k K' j m p : ℕ) : Bool :=
  let N := 5 * k ^ 2 * 693147 ^ 2
  let D := q ^ 2 * 10 ^ 12
  let Ka := (N + D - 1) / D
  decide ((Ka - 1) * D < N) && decide (17 ≤ Ka) && decide (K' ≤ Ka) &&
    decide (K' ^ (j * q) ≤ 2 ^ m) &&
    decide ((m * 27725888 + 13 * q * 10 ^ 7) ^ 2 ≤ Ka * (q * 4 * 10 ^ 7) ^ 2) &&
    decide (2 ^ (k + 1) ≤ chooseB p j ^ q)

theorem block_false {q k K' j m p n M r : ℕ} (hq : 1 ≤ q) (hn : 1 ≤ n)
    (hb : blockOK q k K' j m p = true) (hp : p ≤ Nat.primeCounting K')
    (hk : 2 ^ k ≤ n ^ q) (hk' : n ^ q < 2 ^ (k + 1))
    (hKM : ⌈5 * Real.log n ^ 2⌉₊ ≤ M) (hr : r.Prime)
    (hlt : (M : ℝ) < (Real.log r + 13 / 4) ^ 2)
    (hdvd : ∀ i, 2 ≤ i → i ≤ M → r ∣ i ^ n - 1) : False := by
  simp only [blockOK, Bool.and_eq_true, decide_eq_true_eq] at hb
  obtain ⟨⟨⟨⟨⟨h1, h17⟩, hK'⟩, hpow⟩, hm⟩, hch⟩ := hb
  set N := 5 * k ^ 2 * 693147 ^ 2 with hN
  set D := q ^ 2 * 10 ^ 12 with hD
  set Ka := (N + D - 1) / D with hKa
  have hqR : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hl2 := Real.log_two_gt_d9
  have hl2' := Real.log_two_lt_d9
  -- `k log 2 ≤ q log n`
  have hlogn : (k : ℝ) * 0.693147 ≤ q * Real.log n := by
    have h := Real.log_le_log (by positivity) (by exact_mod_cast hk :
      ((2 ^ k : ℕ) : ℝ) ≤ ((n ^ q : ℕ) : ℝ))
    push_cast at h
    rw [Real.log_pow, Real.log_pow] at h
    have : (k : ℝ) * 0.693147 ≤ k * Real.log 2 := by
      apply mul_le_mul_of_nonneg_left _ (by positivity); linarith
    linarith
  -- `Ka ≤ ⌈5 log² n⌉ ≤ M`
  have hKaM : Ka ≤ M := by
    have hcast : (((Ka - 1 : ℕ) : ℝ)) * D < N := by exact_mod_cast h1
    rw [Nat.cast_sub (by omega)] at hcast
    have hND : (N : ℝ) ≤ 5 * Real.log n ^ 2 * D := by
      rw [hN, hD]; push_cast
      have h0 : 0 ≤ (k : ℝ) * 0.693147 := by positivity
      have hsq : ((k : ℝ) * 0.693147) ^ 2 ≤ (q * Real.log n) ^ 2 := by gcongr
      nlinarith
    have hDpos : (0 : ℝ) < D := by rw [hD]; positivity
    have : (Ka : ℝ) - 1 < 5 * Real.log n ^ 2 := by
      have h' : ((Ka : ℝ) - 1) * D < 5 * Real.log n ^ 2 * D := by
        push_cast at hcast; linarith
      exact lt_of_mul_lt_mul_right h' hDpos.le
    have h2 : 5 * Real.log n ^ 2 ≤ (⌈5 * Real.log n ^ 2⌉₊ : ℝ) := Nat.le_ceil _
    have : (Ka : ℝ) < ⌈5 * Real.log n ^ 2⌉₊ + 1 := by linarith
    have : Ka < ⌈5 * Real.log n ^ 2⌉₊ + 1 := by exact_mod_cast this
    omega
  -- `2^m < r^q`
  have hr1 : (1 : ℝ) < r := by exact_mod_cast hr.one_lt
  have hlogr : 0 < Real.log r := Real.log_pos hr1
  have hmlt : (m : ℝ) * 0.6931472 < q * Real.log r := by
    have hc : (((m * 27725888 + 13 * q * 10 ^ 7) ^ 2 : ℕ) : ℝ) ≤
        ((Ka * (q * 4 * 10 ^ 7) ^ 2 : ℕ) : ℝ) := by exact_mod_cast hm
    push_cast at hc
    set t : ℝ := (m * 0.6931472) / q with ht
    have hsq : (t + 13 / 4) ^ 2 ≤ (Ka : ℝ) := by
      have hq4 : (0 : ℝ) < q * 4 * 10 ^ 7 := by positivity
      have : t + 13 / 4 = (m * 27725888 + 13 * q * 10 ^ 7) / (q * 4 * 10 ^ 7) := by
        rw [ht]; field_simp; ring
      rw [this, div_pow, div_le_iff₀ (by positivity)]
      linarith
    have hKaR : (Ka : ℝ) ≤ M := by exact_mod_cast hKaM
    have h3 : (t + 13 / 4) ^ 2 < (Real.log r + 13 / 4) ^ 2 := by linarith
    have ht0 : 0 ≤ t + 13 / 4 := by rw [ht]; positivity
    have h4 : t + 13 / 4 < Real.log r + 13 / 4 :=
      lt_of_pow_lt_pow_left₀ 2 (by linarith) h3
    have : t < Real.log r := by linarith
    rw [ht, div_lt_iff₀ (by linarith)] at this
    linarith
  have h2m : 2 ^ m < r ^ q := by
    have : ((2 : ℝ)) ^ m < (r : ℝ) ^ q := by
      rw [← Real.log_lt_log_iff (by positivity) (by positivity), Real.log_pow, Real.log_pow]
      have : (m : ℝ) * Real.log 2 ≤ m * 0.6931472 :=
        mul_le_mul_of_nonneg_left (hl2'.trans (by norm_num)).le (by positivity)
      push_cast; linarith
    exact_mod_cast this
  have hKj : K' ^ j < r := by
    have : (K' ^ j) ^ q < r ^ q := by rw [← pow_mul]; exact lt_of_le_of_lt hpow h2m
    exact (Nat.pow_lt_pow_iff_left (by omega)).1 this
  have hcnt := choose_le_of_bad hn hr hdvd K' j (by omega) hKj
  have hpj : p.choose j ≤ n := (Nat.choose_le_choose j hp).trans hcnt
  rw [chooseB_eq] at hch
  have : (p.choose j) ^ q ≤ n ^ q := Nat.pow_le_pow_left hpj q
  omega

/-- Prime counts below `3025` by trial division. -/
def piCount (K : ℕ) : ℕ := ((List.range (K + 1)).filter isPrimeSmall).length

theorem piCount_le {K : ℕ} (hK : K < 3025) : piCount K ≤ Nat.primeCounting K := by
  rw [← Nat.primesLE_card_eq_primeCounting, piCount]
  set l := (List.range (K + 1)).filter isPrimeSmall
  have hnd : l.Nodup := (List.nodup_range).filter _
  rw [← List.toFinset_card_of_nodup hnd]
  apply Finset.card_le_card
  intro x hx
  rw [List.mem_toFinset, List.mem_filter, List.mem_range] at hx
  exact Nat.mem_primesLE.2 ⟨by omega, prime_of_isPrimeSmall (by omega) hx.2⟩

/-- Chebyshev at a power of two: `2^s ≤ s π(2^s)` for `s ≥ 3`. -/
theorem pow_two_le_primeCounting {s : ℕ} (hs : 3 ≤ s) :
    2 ^ s ≤ s * Nat.primeCounting (2 ^ s) := by
  have h7 : 7 ≤ 2 ^ s := by
    calc 7 ≤ 2 ^ 3 := by norm_num
      _ ≤ 2 ^ s := Nat.pow_le_pow_right (by norm_num) hs
  have h1 := Chebyshev.psi_ge_of_seven_le h7
  have h2 := Chebyshev.psi_le_primeCounting_mul_log (2 ^ s)
  push_cast at h1 h2
  rw [Real.log_pow] at h2
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have : (2 : ℝ) ^ s ≤ s * Nat.primeCounting (2 ^ s) := by
    have := h1.trans h2
    nlinarith
  exact_mod_cast this

/-- `p ≤ π(K')`, by counting (`K' < 3025`) or by Chebyshev (`K' = 2^s`). -/
def piOK (K' p : ℕ) : Bool :=
  (decide (K' < 3025) && decide (p ≤ piCount K')) ||
    (List.range 64).any fun s => decide (3 ≤ s) && decide (K' = 2 ^ s) && decide (p * s ≤ K')

theorem le_of_piOK {K' p : ℕ} (h : piOK K' p = true) : p ≤ Nat.primeCounting K' := by
  simp only [piOK, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, List.any_eq_true,
    List.mem_range] at h
  rcases h with ⟨h1, h2⟩ | ⟨s, -, ⟨hs, rfl⟩, hps⟩
  · exact h2.trans (piCount_le h1)
  · have := pow_two_le_primeCounting hs
    have : p * s ≤ Nat.primeCounting (2 ^ s) * s := by linarith
    exact Nat.le_of_mul_le_mul_right this (by omega)

/-- Check consecutive blocks `k₀, k₀ + 1, …` against a list of certificates. -/
def checkList (q : ℕ) : ℕ → List (ℕ × ℕ × ℕ × ℕ) → Bool
  | _, [] => true
  | k, (K', j, m, p) :: l => blockOK q k K' j m p && piOK K' p && checkList q (k + 1) l

theorem checkList_sound {q : ℕ} : ∀ (k₀ : ℕ) (l : List (ℕ × ℕ × ℕ × ℕ)),
    checkList q k₀ l = true → ∀ k, k₀ ≤ k → k < k₀ + l.length →
      ∃ K' j m p, blockOK q k K' j m p = true ∧ p ≤ Nat.primeCounting K'
  | _, [], _, k, h1, h2 => by simp at h2; omega
  | k₀, (K', j, m, p) :: l, h, k, h1, h2 => by
    simp only [checkList, Bool.and_eq_true] at h
    obtain ⟨⟨hb, hpi⟩, hl⟩ := h
    rcases Nat.eq_or_lt_of_le h1 with rfl | hlt
    · exact ⟨K', j, m, p, hb, le_of_piOK hpi⟩
    · exact checkList_sound (k₀ + 1) l hl k (by omega) (by simp at h2; omega)

end Erdos770.Sharp
