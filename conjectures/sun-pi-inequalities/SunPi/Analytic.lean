import Mathlib

/-!
# The analytic half: Chebyshev's bound and a count of residues

Write `P = π(X)` and `Δ = π(X + h) − π(X)`. Then `(P + Δ)^k < P^{k+1}` as soon as
`kΔ < P log P` (`pow_lt_of_mul_lt`), because `log(1 + Δ/P) ≤ Δ/P`.

* `P log P` is bounded below from Mathlib's Chebyshev bound `X log 2 ≤ ψ(X) ≤ π(X) log X`
  (`X ≥ 7`): `P log P ≥ X·(log 2·(1 − 2^{-i}) − (i log 2 − 0.5572)/j)` for `X ≥ 2^j`
  (`PlogP_ge`). The parameter `i` is the tangent point `2^i` of `log L ≤ L/2^i + i log 2 − 1`.
* `Δ` is bounded above by Mathlib's `Nat.primeCounting_add_le`, which counts the integers in
  `(X, X + h]` prime to `a` (`a = 6` for Conjecture 2.7(i), `a = 210` for Conjecture 2.14(ii)).

Both bounds are elementary; nothing here uses RH.
-/

open Real
open scoped Nat.Prime

namespace SunPi

/-- `kΔ < P log P` implies `(P + Δ)^k < P^{k+1}`. -/
theorem pow_lt_of_mul_lt (P Δ k : ℕ) (hP : 1 ≤ P) (h : (k : ℝ) * Δ < P * Real.log P) :
    (P + Δ) ^ k < P ^ (k + 1) := by
  have hP0 : (0 : ℝ) < P := by exact_mod_cast hP
  have hPD : (0 : ℝ) < P + Δ := by positivity
  have hlog : Real.log ((P : ℝ) + Δ) ≤ Real.log P + Δ / P := by
    have h1 : Real.log (((P : ℝ) + Δ) / P) ≤ ((P : ℝ) + Δ) / P - 1 :=
      Real.log_le_sub_one_of_pos (by positivity)
    rw [Real.log_div hPD.ne' hP0.ne'] at h1
    have : ((P : ℝ) + Δ) / P - 1 = Δ / P := by field_simp; ring
    linarith
  have h2 : (k : ℝ) * (Δ / P) < Real.log P := by
    rw [← mul_div_assoc, div_lt_iff₀ hP0]; linarith [mul_comm (Real.log P) (P : ℝ)]
  have hk : (0 : ℝ) ≤ k := by positivity
  have key : (k : ℝ) * Real.log ((P : ℝ) + Δ) < ((k : ℝ) + 1) * Real.log P := by
    nlinarith [mul_le_mul_of_nonneg_left hlog hk]
  have h3 : Real.log (((P : ℝ) + Δ) ^ k) < Real.log ((P : ℝ) ^ (k + 1)) := by
    rw [Real.log_pow, Real.log_pow]; push_cast; linarith
  have h4 := (Real.log_lt_log_iff (by positivity) (by positivity)).mp h3
  exact_mod_cast h4

/-- Chebyshev's lower bound in Mathlib: `X log 2 ≤ π(X) log X` for `X ≥ 7`. -/
theorem cheb (X : ℕ) (hX : 7 ≤ X) : (X : ℝ) * Real.log 2 ≤ π X * Real.log X :=
  (Chebyshev.psi_ge_of_seven_le hX).trans (Chebyshev.psi_le_primeCounting_mul_log X)

theorem log_log_two_ge : -(4428 / 10000 : ℝ) ≤ Real.log (Real.log 2) := by
  have h2 := Real.log_two_gt_d9
  have hpos : 0 < Real.log 2 := by linarith
  have h := Real.one_sub_inv_le_log_of_pos hpos
  have hinv : (Real.log 2)⁻¹ ≤ 14428 / 10000 := by
    rw [inv_le_comm₀ hpos (by norm_num)]; norm_num at h2 ⊢; linarith
  linarith

/-- The lower bound for `P log P` used for both conjectures. -/
theorem PlogP_ge (X j i : ℕ) (hX : 2 ^ j ≤ X) (h7 : 7 ≤ X) (hj : 0 < j) (hi : 1 ≤ i) :
    (X : ℝ) * (Real.log 2 * (1 - (1 / 2 : ℝ) ^ i) - (i * Real.log 2 - 1 + 4428 / 10000) / j)
      ≤ π X * Real.log (π X) := by
  have hl2 := Real.log_two_gt_d9
  have hl2pos : 0 < Real.log 2 := by linarith
  have hX0 : (0 : ℝ) < X := by have : (0 : ℝ) < 7 := by norm_num
                                 exact lt_of_lt_of_le this (by exact_mod_cast h7)
  have hX1 : (1 : ℝ) < X := by
    have : (7 : ℝ) ≤ X := by exact_mod_cast h7
    linarith
  set L := Real.log X with hLdef
  have hLpos : 0 < L := Real.log_pos hX1
  have hjL : (j : ℝ) * Real.log 2 ≤ L := by
    have : Real.log ((2 : ℝ) ^ j) ≤ L :=
      Real.log_le_log (by positivity) (by exact_mod_cast hX)
    rwa [Real.log_pow] at this
  -- P ≥ 1
  have hP1 : 1 ≤ π X := by
    have : π 2 ≤ π X := Nat.monotone_primeCounting (by omega)
    have h2 : π 2 = 1 := by decide
    omega
  set P : ℝ := (π X : ℝ) with hPdef
  have hP1' : (1 : ℝ) ≤ P := by exact_mod_cast hP1
  have hPpos : 0 < P := by linarith
  have hlogP : 0 ≤ Real.log P := Real.log_nonneg hP1'
  -- Q = X log 2 / L ≤ P
  set Q : ℝ := X * Real.log 2 / L with hQdef
  have hQpos : 0 < Q := by positivity
  have hQP : Q ≤ P := by
    rw [hQdef, div_le_iff₀ hLpos]; exact cheb X h7
  -- log Q = L + log log 2 − log L
  have hlogQ : Real.log Q = L + Real.log (Real.log 2) - Real.log L := by
    rw [hQdef, Real.log_div (by positivity) hLpos.ne', Real.log_mul hX0.ne' hl2pos.ne']
  have hlogL : Real.log L ≤ L * (1 / 2 : ℝ) ^ i + i * Real.log 2 - 1 := by
    have h1 := Real.log_le_sub_one_of_pos (x := L * (1 / 2 : ℝ) ^ i) (by positivity)
    rw [Real.log_mul hLpos.ne' (by positivity), one_div, inv_pow, Real.log_inv,
      Real.log_pow] at h1
    rw [one_div, inv_pow]; linarith
  have hll := log_log_two_ge
  set c : ℝ := i * Real.log 2 - 1 + 4428 / 10000 with hc
  have hc0 : 0 ≤ c := by
    have : (1 : ℝ) ≤ i := by exact_mod_cast hi
    rw [hc]; nlinarith
  have hlogQ' : L * (1 - (1 / 2 : ℝ) ^ i) - c ≤ Real.log Q := by
    rw [hlogQ, hc]; linarith
  -- assemble
  have step1 : Q * Real.log Q ≤ P * Real.log P :=
    calc Q * Real.log Q ≤ Q * Real.log P :=
          mul_le_mul_of_nonneg_left (Real.log_le_log hQpos hQP) hQpos.le
      _ ≤ P * Real.log P := mul_le_mul_of_nonneg_right hQP hlogP
  have step2 : Q * (L * (1 - (1 / 2 : ℝ) ^ i) - c) ≤ Q * Real.log Q :=
    mul_le_mul_of_nonneg_left hlogQ' hQpos.le
  have step3 : Q * (L * (1 - (1 / 2 : ℝ) ^ i) - c)
      = X * Real.log 2 * (1 - (1 / 2 : ℝ) ^ i) - X * c * (Real.log 2 / L) := by
    rw [hQdef]; field_simp
  have step4 : X * c * (Real.log 2 / L) ≤ X * c / j := by
    have hjpos : (0 : ℝ) < j := by exact_mod_cast hj
    have : Real.log 2 / L ≤ 1 / j := by
      rw [div_le_div_iff₀ hLpos hjpos]; linarith
    calc (X : ℝ) * c * (Real.log 2 / L) ≤ X * c * (1 / j) :=
          mul_le_mul_of_nonneg_left this (by positivity)
      _ = X * c / j := by ring
  have : (X : ℝ) * (Real.log 2 * (1 - (1 / 2 : ℝ) ^ i) - c / j)
      = X * Real.log 2 * (1 - (1 / 2 : ℝ) ^ i) - X * c / j := by ring
  rw [this]
  linarith

/-- Conjecture 2.7(i) for `kn ≥ 2^j` and `n ≥ s`, given the numerical condition of region
`(j, s, i)`. The count of integers prime to 6 gives `kΔ ≤ kn/3 + 2k`. -/
theorem sunA_region (n k j s i : ℕ) (hk1 : 1 ≤ k) (hkn : k ≤ n) (hX : 2 ^ j ≤ k * n)
    (hj : 3 ≤ j) (hs : s ≤ n) (hs0 : 0 < s) (hi : 1 ≤ i)
    (hnum : (1 : ℝ) / 3 + 2 / s
      < Real.log 2 * (1 - (1 / 2 : ℝ) ^ i) - (i * Real.log 2 - 1 + 4428 / 10000) / j) :
    π ((k + 1) * n) ^ k < π (k * n) ^ (k + 1) := by
  have h8 : 8 ≤ k * n := le_trans (by
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) hj) hX
  set X := k * n with hXdef
  have hsucc : (k + 1) * n = X + n := by rw [hXdef]; ring
  have hadd : π (X + n) ≤ π X + Nat.totient 6 * (n / 6 + 1) :=
    Nat.primeCounting_add_le (by norm_num) (by omega) n
  have ht6 : Nat.totient 6 = 2 := by decide
  rw [ht6] at hadd
  have hmono : π X ≤ π (X + n) := Nat.monotone_primeCounting (by omega)
  set Δ := π (X + n) - π X with hΔ
  have hPD : π X + Δ = π (X + n) := by omega
  have hP1 : 1 ≤ π X := by
    have : π 2 ≤ π X := Nat.monotone_primeCounting (by omega)
    have h2 : π 2 = 1 := by decide
    omega
  rw [hsucc, ← hPD]
  apply pow_lt_of_mul_lt _ _ _ hP1
  have hΔle : (Δ : ℝ) ≤ n / 3 + 2 := by
    have h1 : Δ ≤ 2 * (n / 6) + 2 := by omega
    have h2 : ((n / 6 : ℕ) : ℝ) ≤ (n : ℝ) / 6 := Nat.cast_div_le
    have h1' : (Δ : ℝ) ≤ 2 * ((n / 6 : ℕ) : ℝ) + 2 := by exact_mod_cast h1
    linarith
  have hXr : (X : ℝ) = k * n := by rw [hXdef]; push_cast; ring
  have hk0 : (0 : ℝ) ≤ k := by positivity
  have hkΔ : (k : ℝ) * Δ ≤ X / 3 + 2 * k := by
    rw [hXr]; nlinarith [mul_le_mul_of_nonneg_left hΔle hk0]
  have hks : (k : ℝ) * s ≤ X := by
    rw [hXr]; exact mul_le_mul_of_nonneg_left (by exact_mod_cast hs) hk0
  have hspos : (0 : ℝ) < s := by exact_mod_cast hs0
  have h2k : 2 * (k : ℝ) ≤ X * (2 / s) := by
    rw [mul_div_assoc', le_div_iff₀ hspos]; linarith
  have hX0 : (0 : ℝ) < X := by
    have : (8 : ℝ) ≤ X := by exact_mod_cast h8
    linarith
  have hlow := PlogP_ge X j i hX (by omega) (by omega) hi
  have : (X : ℝ) * (1 / 3 + 2 / s) < (X : ℝ) * (Real.log 2 * (1 - (1 / 2 : ℝ) ^ i) -
      (i * Real.log 2 - 1 + 4428 / 10000) / j) := mul_lt_mul_of_pos_left hnum hX0
  nlinarith

/-- Conjecture 2.14(ii) for `n² ≥ 2^j` and `n ≥ s`, given the numerical condition of region
`(j, s, i)`. The count of integers prime to 210 gives `nΔ ≤ (96/210) n² + (48 + 48/210) n`. -/
theorem sunB_region (n j s i : ℕ) (hX : 2 ^ j ≤ n * n) (hj : 8 ≤ j) (hs : s ≤ n) (hs0 : 0 < s)
    (hi : 1 ≤ i)
    (hnum : (96 : ℝ) / 210 + (48 + 48 / 210) / s
      < Real.log 2 * (1 - (1 / 2 : ℝ) ^ i) - (i * Real.log 2 - 1 + 4428 / 10000) / j) :
    π ((n + 1) * (n + 1)) ^ n < π (n * n) ^ (n + 1) := by
  have h256 : 256 ≤ n * n := le_trans (by
    calc 256 = 2 ^ 8 := by norm_num
      _ ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) hj) hX
  set X := n * n with hXdef
  have hsucc : (n + 1) * (n + 1) = X + (2 * n + 1) := by rw [hXdef]; ring
  have hadd : π (X + (2 * n + 1)) ≤ π X + Nat.totient 210 * ((2 * n + 1) / 210 + 1) :=
    Nat.primeCounting_add_le (by norm_num) (by omega) _
  have ht : Nat.totient 210 = 48 := by decide
  rw [ht] at hadd
  have hmono : π X ≤ π (X + (2 * n + 1)) := Nat.monotone_primeCounting (by omega)
  set Δ := π (X + (2 * n + 1)) - π X with hΔ
  have hPD : π X + Δ = π (X + (2 * n + 1)) := by omega
  have hP1 : 1 ≤ π X := by
    have : π 2 ≤ π X := Nat.monotone_primeCounting (by omega)
    have h2 : π 2 = 1 := by decide
    omega
  rw [hsucc, ← hPD]
  apply pow_lt_of_mul_lt _ _ _ hP1
  have hΔle : (Δ : ℝ) ≤ 48 * ((2 * n + 1) / 210) + 48 := by
    have h1 : Δ ≤ 48 * ((2 * n + 1) / 210) + 48 := by omega
    have h2 : (((2 * n + 1) / 210 : ℕ) : ℝ) ≤ ((2 * n + 1 : ℕ) : ℝ) / 210 := Nat.cast_div_le
    have h1' : (Δ : ℝ) ≤ 48 * (((2 * n + 1) / 210 : ℕ) : ℝ) + 48 := by exact_mod_cast h1
    push_cast at h2
    linarith
  have hXr : (X : ℝ) = n * n := by rw [hXdef]; push_cast; ring
  have hn0 : (0 : ℝ) ≤ n := by positivity
  have hnΔ : (n : ℝ) * Δ ≤ X * (96 / 210) + n * (48 + 48 / 210) := by
    rw [hXr]; nlinarith [mul_le_mul_of_nonneg_left hΔle hn0]
  have hns : (n : ℝ) * s ≤ X := by
    rw [hXr]; exact mul_le_mul_of_nonneg_left (by exact_mod_cast hs) hn0
  have hspos : (0 : ℝ) < s := by exact_mod_cast hs0
  have h2k : (n : ℝ) * (48 + 48 / 210) ≤ X * ((48 + 48 / 210) / s) := by
    rw [mul_div_assoc', le_div_iff₀ hspos]; nlinarith
  have hX0 : (0 : ℝ) < X := by
    have : (256 : ℝ) ≤ X := by exact_mod_cast h256
    linarith
  have hlow := PlogP_ge X j i hX (by omega) (by omega) hi
  have : (X : ℝ) * (96 / 210 + (48 + 48 / 210) / s) < (X : ℝ) * (Real.log 2 *
      (1 - (1 / 2 : ℝ) ^ i) - (i * Real.log 2 - 1 + 4428 / 10000) / j) :=
    mul_lt_mul_of_pos_left hnum hX0
  nlinarith

end SunPi
