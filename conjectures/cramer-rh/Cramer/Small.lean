import Mathlib

/-!
# The range `2 ≤ x < 10^6`: a prime in `(x, x + 2√x log x]` by a checked prime chain

`primeChain` is a list of 99 primes `2 = q₀ < q₁ < … < q_98 = 1005161`, each paired with
`j = ⌊log₂ q⌋`. `chainOK` checks `2^j ≤ q_i` and `(q_{i+1} − q_i)² · 10⁶ ≤ 4 q_i (693 j)²`, which
gives `q_{i+1} − q_i ≤ 2 · 0.693 j √q_i ≤ 2 √q_i log q_i` (`gap_le`). The check is evaluated by
`decide` in the kernel (no `native_decide`); primality of each entry is proved by `norm_num`.
A prime in `(x, x + 2√x log x]` then follows by walking the chain (`exists_prime_of_chain`).
The list was generated greedily (largest admissible prime at each step).
-/

namespace Cramer

open Real

/-- The checked chain of primes, each with `⌊log₂ q⌋`. -/
def primeChain : List (ℕ × ℕ) := [
  (2, 1), (3, 1), (5, 2), (11, 3), (23, 4), (47, 5),
  (89, 6), (167, 7), (283, 8), (467, 8), (701, 9), (1031, 10),
  (1471, 10), (1999, 10), (2617, 11), (3391, 11), (4273, 12), (5351, 12),
  (6563, 12), (7907, 12), (9377, 13), (11119, 13), (13009, 13), (15061, 13),
  (17257, 14), (19801, 14), (22531, 14), (25439, 14), (28517, 14), (31793, 14),
  (35251, 15), (39139, 15), (43237, 15), (47543, 15), (52069, 15), (56809, 15),
  (61757, 15), (66923, 16), (72649, 16), (78623, 16), (84827, 16), (91283, 16),
  (97973, 16), (104911, 16), (112087, 16), (119503, 16), (127163, 16), (135059, 17),
  (143711, 17), (152641, 17), (161839, 17), (171317, 17), (181063, 17), (191071, 17),
  (201359, 17), (211931, 17), (222773, 17), (233881, 17), (245269, 17), (256931, 17),
  (268861, 18), (281791, 18), (295033, 18), (308573, 18), (322429, 18), (336593, 18),
  (351061, 18), (365839, 18), (380917, 18), (396311, 18), (412007, 18), (428003, 18),
  (444307, 18), (460919, 18), (477847, 18), (495071, 18), (512621, 18), (530447, 19),
  (549623, 19), (569141, 19), (588977, 19), (609179, 19), (629723, 19), (650609, 19),
  (671837, 19), (693421, 19), (715339, 19), (737593, 19), (760187, 19), (783143, 19),
  (806447, 19), (830051, 19), (854041, 19), (878377, 19), (903037, 19), (928051, 19),
  (953399, 19), (979109, 19), (1005161, 19)]

/-- The arithmetic check: `2^j ≤ p` at every node, and the gap condition between neighbours. -/
def chainOK : ℕ × ℕ → List (ℕ × ℕ) → Bool
  | (p, j), [] => decide (2 ^ j ≤ p)
  | (p, j), (q, k) :: l =>
      decide (2 ^ j ≤ p) && decide (p < q) && decide ((q - p) ^ 2 * 10 ^ 6 ≤ 4 * p * (693 * j) ^ 2)
        && chainOK (q, k) l

/-- The last prime of a chain. -/
def lastP (p : ℕ) : List (ℕ × ℕ) → ℕ
  | [] => p
  | e :: l => lastP e.1 l

theorem primeChain_ok : chainOK (2, 1) primeChain.tail = true := by decide

theorem primeChain_head : primeChain = (2, 1) :: primeChain.tail := rfl

theorem primeChain_last : lastP 2 primeChain.tail = 1005161 := by decide

theorem primeChain_prime : ∀ e ∈ primeChain, e.1.Prime := by
  simp only [primeChain, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
  refine ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩

/-- `2^j ≤ p` gives `0.693 j ≤ log p`. -/
lemma log_ge_of_pow_le {p j : ℕ} (hp : 2 ^ j ≤ p) : 0.693 * (j : ℝ) ≤ Real.log p := by
  have h1 : Real.log ((2 : ℝ) ^ j) ≤ Real.log p :=
    Real.log_le_log (by positivity) (by exact_mod_cast hp)
  rw [Real.log_pow] at h1
  have := Real.log_two_gt_d9
  have hj : (0 : ℝ) ≤ j := j.cast_nonneg
  nlinarith

/-- The gap condition implies `q ≤ p + 2 √p log p`. -/
lemma gap_le {p q j : ℕ} (hp : 2 ^ j ≤ p) (hpq : p < q)
    (hg : (q - p) ^ 2 * 10 ^ 6 ≤ 4 * p * (693 * j) ^ 2) :
    (q : ℝ) ≤ p + 2 * √(p : ℝ) * Real.log p := by
  have hlog := log_ge_of_pow_le hp
  set X := 2 * √(p : ℝ) * (0.693 * j) with hX
  have hX0 : 0 ≤ X := by positivity
  have hg' : ((q : ℝ) - p) ^ 2 ≤ X ^ 2 := by
    have h1 : (((q - p) ^ 2 * 10 ^ 6 : ℕ) : ℝ) ≤ ((4 * p * (693 * j) ^ 2 : ℕ) : ℝ) := by
      exact_mod_cast hg
    push_cast [Nat.cast_sub hpq.le] at h1
    rw [hX, mul_pow, mul_pow, Real.sq_sqrt (by positivity)]
    nlinarith
  have hq : (q : ℝ) - p ≤ X := by
    by_contra hc
    push Not at hc
    nlinarith
  have : X ≤ 2 * √(p : ℝ) * Real.log p :=
    mul_le_mul_of_nonneg_left hlog (by positivity)
  linarith

/-- `x ↦ x + 2√x log x` is monotone on `[1, ∞)`. -/
lemma step_mono {p y : ℝ} (hp : 1 ≤ p) (hpy : p ≤ y) :
    p + 2 * √p * Real.log p ≤ y + 2 * √y * Real.log y := by
  have h1 : √p ≤ √y := Real.sqrt_le_sqrt hpy
  have h2 : Real.log p ≤ Real.log y := Real.log_le_log (by linarith) hpy
  have h3 : 0 ≤ Real.log p := Real.log_nonneg hp
  have h4 : 0 ≤ √p := Real.sqrt_nonneg _
  have h5 : √p * Real.log p ≤ √y * Real.log y :=
    mul_le_mul h1 h2 h3 (by linarith)
  linarith

/-- Walking a checked chain. -/
theorem exists_prime_of_chain : ∀ (L : List (ℕ × ℕ)) (p j : ℕ), chainOK (p, j) L = true →
    p.Prime → (∀ e ∈ L, e.1.Prime) → ∀ y : ℝ, (p : ℝ) ≤ y → y < lastP p L →
    ∃ q : ℕ, q.Prime ∧ y < q ∧ (q : ℝ) ≤ y + 2 * √y * Real.log y
  | [], p, j, _, _, _, y, hpy, hy => by simp [lastP] at hy; linarith
  | (q, k) :: l, p, j, hc, hp, hl, y, hpy, hy => by
    simp only [chainOK, Bool.and_eq_true, decide_eq_true_eq] at hc
    obtain ⟨⟨⟨hpj, hpq⟩, hg⟩, hc'⟩ := hc
    have hq : q.Prime := hl (q, k) (by simp)
    rcases lt_or_ge y q with h | h
    · refine ⟨q, hq, h, ?_⟩
      have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp.one_lt.le
      exact (gap_le hpj hpq hg).trans (step_mono hp1 hpy)
    · exact exists_prime_of_chain l q k hc' hq (fun e he => hl e (by simp [he])) y h
        (by simpa [lastP] using hy)

/-- **Every `(x, x + 2√x log x]` with `2 ≤ x < 10^6` contains a prime** (no hypothesis). -/
theorem exists_prime_small {x : ℝ} (hx2 : 2 ≤ x) (hx : x < 10 ^ 6) :
    ∃ p : ℕ, p.Prime ∧ x < p ∧ (p : ℝ) ≤ x + 2 * √x * Real.log x := by
  have hall := primeChain_prime
  rw [primeChain_head] at hall
  refine exists_prime_of_chain primeChain.tail 2 1 primeChain_ok Nat.prime_two
    (fun e he => hall e (List.mem_cons_of_mem _ he)) x (by norm_num; linarith) ?_
  rw [primeChain_last]; push_cast; linarith

end Cramer
