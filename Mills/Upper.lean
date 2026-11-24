import Mathlib
import Mills.Greedy

/-!
# The greedy limit is a Mills number, given primes between cubes

`PrimeBetweenCubes x₀` is the single analytic input: every `x ≥ x₀` has a prime strictly between
`x^3` and `(x+1)^3`.  Under RH this follows from Schoenfeld's explicit bound on `ψ`
(Caldwell–Cheng use `x₀ = 2657`); here it is a named hypothesis.

The greedy sequence only ever needs it at the points `x = g n` with `n ≥ 3`, i.e. at
`x ≥ g 3 = 2521008887`.  The three steps below that, `2 → 11 → 1361 → 2521008887`, are checked
directly (`g_one`, `g_two`, `g_three`), so **no cube range below `2521008887` ever needs the
hypothesis**; any `x₀ ≤ 2521008887` works.

From the hypothesis we get `g (n+1) < (g n + 1)^3`, so `P_n^{1/3^n}` increases and
`(P_n+1)^{1/3^n}` strictly decreases, the supremum `A` of the first is a Mills number, and
`A ≤ (P_4+1)^{1/81}`.
-/

set_option linter.constructorNameAsVariable false

namespace Mills

/-- The analytic input (Caldwell–Cheng, Lemma 5 under RH): for every `x ≥ x₀` there is a prime
strictly between `x^3` and `(x+1)^3`. -/
def PrimeBetweenCubes (x₀ : ℕ) : Prop :=
  ∀ x : ℕ, x₀ ≤ x → ∃ p : ℕ, p.Prime ∧ x ^ 3 < p ∧ p < (x + 1) ^ 3

/-- Each greedy step stays below the next cube. -/
theorem g_succ_lt {x₀ : ℕ} (h : PrimeBetweenCubes x₀) (hx : x₀ ≤ 2521008887) (n : ℕ) :
    g (n + 1) < (g n + 1) ^ 3 := by
  by_cases hn : 3 ≤ n
  · have h3 : x₀ ≤ g n := le_trans hx (by rw [← g_three]; exact g_mono hn)
    obtain ⟨p, hp, hp1, hp2⟩ := h (g n) h3
    rw [g_succ]
    exact lt_of_le_of_lt (nextPrime_le hp hp1.le) hp2
  · interval_cases n
    · rw [g_one, g_zero]; norm_num
    · rw [g_two, g_one]; norm_num
    · rw [g_three, g_two]; norm_num

/-- The strict form: `g (n+1) + 1 < (g n + 1)^3`, since `(g n + 1)^3 - 1 = g n * (…)` is composite. -/
theorem g_succ_add_one_lt {x₀ : ℕ} (h : PrimeBetweenCubes x₀) (hx : x₀ ≤ 2521008887) (n : ℕ) :
    g (n + 1) + 1 < (g n + 1) ^ 3 := by
  have hlt := g_succ_lt h hx n
  have hne : g (n + 1) + 1 ≠ (g n + 1) ^ 3 := by
    intro heq
    have hfac : g (n + 1) = g n * (g n ^ 2 + 3 * g n + 3) := by
      have : g (n + 1) + 1 = g n * (g n ^ 2 + 3 * g n + 3) + 1 := by rw [heq]; ring
      omega
    have hp := g_prime (n + 1)
    rw [hfac, Nat.prime_mul_iff] at hp
    have h2 := (g_prime n).two_le
    rcases hp with ⟨_, h1⟩ | ⟨_, h1⟩
    · nlinarith
    · omega
  omega

/-! ### Real roots -/

lemma root_pow (x : ℝ) (hx : 0 ≤ x) (m : ℕ) (hm : m ≠ 0) : (x ^ ((1 : ℝ) / m)) ^ m = x := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hx]
  have : (1 : ℝ) / m * m = 1 := by field_simp
  rw [this, Real.rpow_one]

/-- `P_{n+1}^{1/3^{n+1}}`. -/
noncomputable def lo (n : ℕ) : ℝ := (g n : ℝ) ^ ((1 : ℝ) / ((3 ^ (n + 1) : ℕ) : ℝ))

/-- `(P_{n+1}+1)^{1/3^{n+1}}`. -/
noncomputable def hi (n : ℕ) : ℝ := ((g n : ℝ) + 1) ^ ((1 : ℝ) / ((3 ^ (n + 1) : ℕ) : ℝ))

lemma lo_pos (n : ℕ) : 0 < lo n :=
  Real.rpow_pos_of_pos (by exact_mod_cast (g_prime n).pos) _

lemma hi_pos (n : ℕ) : 0 < hi n :=
  Real.rpow_pos_of_pos (by have := (g_prime n).pos; positivity) _

lemma lo_pow (n : ℕ) : lo n ^ 3 ^ (n + 1) = g n :=
  root_pow _ (by positivity) _ (by positivity)

lemma hi_pow (n : ℕ) : hi n ^ 3 ^ (n + 1) = (g n : ℝ) + 1 :=
  root_pow _ (by positivity) _ (by positivity)

lemma lo_le_hi (n : ℕ) : lo n ≤ hi n := by
  refine (pow_le_pow_iff_left₀ (lo_pos n).le (hi_pos n).le (by positivity : 3 ^ (n + 1) ≠ 0)).mp ?_
  rw [lo_pow, hi_pow]; linarith

lemma lo_succ_pow (n : ℕ) : lo n ^ 3 ^ (n + 2) = (g n : ℝ) ^ 3 := by
  rw [pow_succ 3 (n + 1), pow_mul, lo_pow]

lemma hi_succ_pow (n : ℕ) : hi n ^ 3 ^ (n + 2) = ((g n : ℝ) + 1) ^ 3 := by
  rw [pow_succ 3 (n + 1), pow_mul, hi_pow]

lemma lo_mono : Monotone lo := by
  refine monotone_nat_of_le_succ fun n => ?_
  refine (pow_le_pow_iff_left₀ (lo_pos n).le (lo_pos (n + 1)).le
    (by positivity : 3 ^ (n + 2) ≠ 0)).mp ?_
  rw [lo_succ_pow, lo_pow]
  exact_mod_cast g_cube_le n

lemma hi_anti {x₀ : ℕ} (h : PrimeBetweenCubes x₀) (hx : x₀ ≤ 2521008887) : Antitone hi := by
  refine antitone_nat_of_succ_le fun n => ?_
  refine (pow_le_pow_iff_left₀ (hi_pos (n + 1)).le (hi_pos n).le
    (by positivity : 3 ^ (n + 2) ≠ 0)).mp ?_
  rw [hi_succ_pow, hi_pow]
  have := g_succ_add_one_lt h hx n
  have h2 : ((g (n + 1) : ℝ) + 1) < ((g n : ℝ) + 1) ^ 3 := by exact_mod_cast this
  exact h2.le

lemma lo_le_hi' {x₀ : ℕ} (h : PrimeBetweenCubes x₀) (hx : x₀ ≤ 2521008887) (n m : ℕ) :
    lo n ≤ hi m :=
  calc lo n ≤ lo (max n m) := lo_mono (le_max_left _ _)
    _ ≤ hi (max n m) := lo_le_hi _
    _ ≤ hi m := hi_anti h hx (le_max_right _ _)

/-- The greedy limit. -/
noncomputable def greedyLimit : ℝ := ⨆ n, lo n

lemma lo_le_limit {x₀ : ℕ} (h : PrimeBetweenCubes x₀) (hx : x₀ ≤ 2521008887) (n : ℕ) :
    lo n ≤ greedyLimit :=
  le_ciSup ⟨hi 0, by rintro _ ⟨m, rfl⟩; exact lo_le_hi' h hx m 0⟩ n

lemma limit_le_hi {x₀ : ℕ} (h : PrimeBetweenCubes x₀) (hx : x₀ ≤ 2521008887) (m : ℕ) :
    greedyLimit ≤ hi m :=
  ciSup_le fun n => lo_le_hi' h hx n m

lemma limit_nonneg {x₀ : ℕ} (h : PrimeBetweenCubes x₀) (hx : x₀ ≤ 2521008887) :
    0 ≤ greedyLimit :=
  le_trans (lo_pos 0).le (lo_le_limit h hx 0)

theorem floor_greedyLimit {x₀ : ℕ} (h : PrimeBetweenCubes x₀) (hx : x₀ ≤ 2521008887) (k : ℕ) :
    ⌊greedyLimit ^ 3 ^ (k + 1)⌋₊ = g k := by
  rw [Nat.floor_eq_iff (pow_nonneg (limit_nonneg h hx) _)]
  constructor
  · calc (g k : ℝ) = lo k ^ 3 ^ (k + 1) := (lo_pow k).symm
      _ ≤ _ := pow_le_pow_left₀ (lo_pos k).le (lo_le_limit h hx k) _
  · have h1 : greedyLimit ^ 3 ^ (k + 1) ≤ hi (k + 1) ^ 3 ^ (k + 1) :=
      pow_le_pow_left₀ (limit_nonneg h hx)
        (limit_le_hi h hx (k + 1)) _
    have h2 : (hi (k + 1) ^ 3 ^ (k + 1)) ^ 3 < ((g k : ℝ) + 1) ^ 3 := by
      rw [← pow_mul, ← pow_succ, hi_pow]
      have := g_succ_add_one_lt h hx k
      exact_mod_cast this
    have h3 : hi (k + 1) ^ 3 ^ (k + 1) < (g k : ℝ) + 1 :=
      lt_of_pow_lt_pow_left₀ 3 (by positivity) h2
    linarith

theorem one_lt_greedyLimit {x₀ : ℕ} (h : PrimeBetweenCubes x₀) (hx : x₀ ≤ 2521008887) :
    1 < greedyLimit := by
  have h0 := lo_le_limit h hx 0
  have h1 : 1 < lo 0 := by
    by_contra hle
    push Not at hle
    have : lo 0 ^ 3 ^ (0 + 1) ≤ 1 := pow_le_one₀ (lo_pos 0).le hle
    rw [lo_pow, g_zero] at this
    norm_num at this
  linarith

/-- **The greedy limit is a Mills number** (given primes between cubes above `x₀`). -/
theorem isMills_greedyLimit {x₀ : ℕ} (h : PrimeBetweenCubes x₀) (hx : x₀ ≤ 2521008887) :
    IsMills greedyLimit := by
  intro n
  obtain ⟨k, hk⟩ : ∃ k : ℕ, (n : ℕ) = k + 1 := ⟨(n : ℕ) - 1, by have := n.pos; omega⟩
  rw [hk, floor_greedyLimit h hx k]
  exact Nat.prime_iff.mp (g_prime k)

/-- `A^81 ≤ P_4 + 1 = 2521008888`. -/
theorem greedyLimit_pow_le {x₀ : ℕ} (h : PrimeBetweenCubes x₀) (hx : x₀ ≤ 2521008887) :
    greedyLimit ^ 81 ≤ 2521008888 := by
  have h1 : greedyLimit ^ 3 ^ (3 + 1) ≤ hi 3 ^ 3 ^ (3 + 1) :=
    pow_le_pow_left₀ (limit_nonneg h hx)
      (limit_le_hi h hx 3) _
  rw [hi_pow, g_three] at h1
  norm_num at h1 ⊢
  linarith

end Mills
