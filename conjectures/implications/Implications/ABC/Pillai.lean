import Implications.ABC.Gcd

/-!
# abc implies Pillai's conjecture

`PillaisConjecture` is the statement of theorem `Catalan.pillais_conjecture` in
formal-conjectures `FormalConjectures/Wikipedia/Catalan.lean` (commit
`9097e2f90e66d2f6244209cb1c07f7120d17ec53`, Apache-2.0, © 2025 The Formal Conjectures Authors),
with its arguments `(a b c : ℕ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)` made into `∀`. It is
open there. The subtraction is in `ℕ`, but since `c > 0` a solution satisfies
`a xⁿ = b y^m + c` exactly, so there are no junk solutions.

Deduction (folklore, the standard abc argument; unverified against a specific source): write
`T = a xⁿ = b y^m + c`. abc in constant form applied to `b y^m + c = T` after dividing out the
gcd (`lt_of_constantMul`, with `rad(b y^m) ≤ b y`, `rad(a xⁿ) ≤ a x`) gives
`T < K (x y · abc)^(1+1/10)`. Since `m, n ≥ 2` and `(m, n) ≠ (2, 2)`, `(xy)^6 ≤ T^5`
(`1/m + 1/n ≤ 5/6`), so `rpow_lt_of_sixth` gives `T^(1/12) < K (abc)^(11/10)`. This bounds `T`,
hence `x, y` and (as `x, y ≥ 2`) `m, n`.
-/

namespace Implications.Abc.Pillai

open _root_.ABC

/-- `Catalan.pillais_conjecture` (`FormalConjectures/Wikipedia/Catalan.lean`), statement verbatim:
For positive integers a, b, and c, there are only finitely many positive solutions (x, y, m, n) to
the equation $ax^n - by^m = c$ where $(m, n) \neq (2, 2)$ and $x, y > 1$. -/
def PillaisConjecture : Prop :=
  ∀ (a b c : ℕ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c),
    { (x, y, m, n) : (ℕ × ℕ × ℕ × ℕ) |
      1 < x ∧ 1 < y ∧ 1 < m ∧ 1 < n ∧ (m, n) ≠ (2, 2) ∧
      a * x^n - b * y^m = c }.Finite

/-- `(xy)^6 ≤ T^5` when `xⁿ ≤ T`, `y^m ≤ T`, `m, n ≥ 2`, `(m, n) ≠ (2, 2)`. -/
lemma mul_pow_six_le {x y m n T : ℕ} (hx : 0 < x) (hy : 0 < y) (hm : 1 < m) (hn : 1 < n)
    (hmn : (m, n) ≠ (2, 2)) (hxT : x ^ n ≤ T) (hyT : y ^ m ≤ T) : (x * y) ^ 6 ≤ T ^ 5 := by
  have hx2 : x ^ 2 ≤ T := (Nat.pow_le_pow_right hx hn).trans hxT
  have hy2 : y ^ 2 ≤ T := (Nat.pow_le_pow_right hy hm).trans hyT
  by_cases h3 : 3 ≤ n
  · have hx3 : x ^ 3 ≤ T := (Nat.pow_le_pow_right hx h3).trans hxT
    calc (x * y) ^ 6 = (x ^ 3) ^ 2 * (y ^ 2) ^ 3 := by ring
      _ ≤ T ^ 2 * T ^ 3 := by gcongr
      _ = T ^ 5 := by ring
  · have hn2 : n = 2 := by omega
    have h3m : 3 ≤ m := by
      by_contra h; apply hmn; ext <;> simp <;> omega
    have hy3 : y ^ 3 ≤ T := (Nat.pow_le_pow_right hy h3m).trans hyT
    calc (x * y) ^ 6 = (x ^ 2) ^ 3 * (y ^ 3) ^ 2 := by ring
      _ ≤ T ^ 3 * T ^ 2 := by gcongr
      _ = T ^ 5 := by ring

/-- **abc implies Pillai's conjecture** (`Catalan.pillais_conjecture`), from the constant form. -/
theorem pillai_of_abcConstantMul (hK : ABCConstantMul) : PillaisConjecture := by
  intro a b c ha hb hc
  set δ : ℝ := 1 / 10 with hδdef
  have hδ0 : 0 < δ := by norm_num
  obtain ⟨K, hK⟩ := hK δ hδ0
  set L : ℝ := K * ((a * b * c : ℕ) : ℝ) ^ (1 + δ)
  set N : ℕ := ⌈L ^ (12 : ℕ)⌉₊
  -- every solution has `T = a xⁿ < N`
  have hbound : ∀ x y m n : ℕ, 0 < x → 0 < y → 1 < m → 1 < n → (m, n) ≠ (2, 2) →
      a * x ^ n = b * y ^ m + c → a * x ^ n < N := by
    intro x y m n hx hy hm hn hmn heq
    set T := a * x ^ n with hT
    have hlt := lt_of_constantMul hK hδ0 (A := b * y ^ m) (B := c) (P := b * y) (Q := a * x)
      (by positivity) hc
      ((radical_mul_le (by positivity) (by positivity)).trans (Nat.mul_le_mul
        (radical_le_self (by omega)) (by rw [radical_pow (by omega)]; exact radical_le_self (by omega))))
      (by
        rw [← heq]
        exact (radical_mul_le (by positivity) (by positivity)).trans (Nat.mul_le_mul
          (radical_le_self (by omega))
          (by rw [radical_pow (by omega)]; exact radical_le_self (by omega))))
    rw [← heq] at hlt
    have hxT : x ^ n ≤ T := Nat.le_mul_of_pos_left _ ha
    have hyT : y ^ m ≤ T := by
      have : y ^ m ≤ b * y ^ m := Nat.le_mul_of_pos_left _ hb
      omega
    have hT1 : (1 : ℝ) ≤ T := by
      have : 1 ≤ T := le_trans (Nat.one_le_pow _ _ hx) hxT
      exact_mod_cast this
    have h6 : (((x * y : ℕ) : ℝ)) ^ 6 ≤ (T : ℝ) ^ 5 := by
      exact_mod_cast mul_pow_six_le hx hy hm hn hmn hxT hyT
    have hlt' : (T : ℝ) < K * (((x * y : ℕ) : ℝ) * ((a * b * c : ℕ) : ℝ)) ^ (1 + δ) := by
      convert hlt using 3; push_cast; ring
    have hu := rpow_lt_of_sixth hT1 (Nat.cast_nonneg _) (Nat.cast_nonneg _) hδ0 h6 hlt'
    rw [show (1 - 5 * δ) / 6 = ((12 : ℕ) : ℝ)⁻¹ by rw [hδdef]; norm_num] at hu
    have hT0 : (0 : ℝ) ≤ T := by linarith
    have h12 : ((T : ℝ) ^ ((12 : ℕ) : ℝ)⁻¹) ^ (12 : ℕ) < L ^ (12 : ℕ) :=
      pow_lt_pow_left₀ hu (Real.rpow_nonneg hT0 _) (by norm_num)
    rw [Real.rpow_inv_natCast_pow hT0 (by norm_num)] at h12
    have : (T : ℝ) < N := h12.trans_le (Nat.le_ceil _)
    exact_mod_cast this
  refine ((Set.finite_Iio N).prod ((Set.finite_Iio N).prod
    ((Set.finite_Iio N).prod (Set.finite_Iio N)))).subset ?_
  rintro ⟨x, y, m, n⟩ ⟨hx, hy, hm, hn, hmn, heq⟩
  have heq' : a * x ^ n = b * y ^ m + c := by omega
  have hT := hbound x y m n (by omega) (by omega) hm hn hmn heq'
  have hxT : x ^ n ≤ a * x ^ n := Nat.le_mul_of_pos_left _ ha
  have hyT : y ^ m ≤ b * y ^ m := Nat.le_mul_of_pos_left _ hb
  have hx1 : x ≤ x ^ n := Nat.le_self_pow (by omega) x
  have hy1 : y ≤ y ^ m := Nat.le_self_pow (by omega) y
  have hn1 : n < 2 ^ n := Nat.lt_two_pow_self
  have hm1 : m < 2 ^ m := Nat.lt_two_pow_self
  have hn2 : 2 ^ n ≤ x ^ n := Nat.pow_le_pow_left hx n
  have hm2 : 2 ^ m ≤ y ^ m := Nat.pow_le_pow_left hy m
  simp only [Set.mem_prod, Set.mem_Iio]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> omega

/-- **abc implies Pillai's conjecture** (`Catalan.pillais_conjecture`), from `ABC.abc` itself. -/
theorem pillai_of_abc (habc : ABCConjecture) : PillaisConjecture :=
  pillai_of_abcConstantMul (abcConstantMul_of_abc habc)

end Implications.Abc.Pillai
