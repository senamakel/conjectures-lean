import Implications.ABC.Gcd

/-!
# abc implies the weak Hall conjecture

`HallIneq`, `HallConjectureExp` are copied verbatim from formal-conjectures
`FormalConjectures/Wikipedia/Hall.lean` (commit `9097e2f90e66d2f6244209cb1c07f7120d17ec53`,
Apache-2.0, © 2025 The Formal Conjectures Authors), and `WeakHallConjecture` is the statement of
theorem `Hall.weak_hall_conjecture` there, with its arguments `(ε : ℝ) (hε : ε > 0)` made into
`∀`. It is open in formal-conjectures.

Deduction (folklore; e.g. Granville–Tucker, *Notices AMS* 49 (2002), unverified): put
`X = |x|`, `Y = |y|`, `D = |y² − x³| ≥ 1`. If `X ≤ D` the bound is immediate (for `x ≤ 0` this
always holds). Otherwise `x > 0`, `y ≠ 0`, and abc in constant form applied to
`min(X³, Y²) + D = max(X³, Y²) =: M` after dividing out the gcd (`lt_of_constantMul`) gives
`M < K (X Y D)^(1+δ)`. Since `(XY)^6 ≤ M^5` this gives `M^((1-5δ)/6) < K D^(1+δ)`
(`rpow_lt_of_sixth`), and `X³ ≤ M` turns it into `X^((1-5δ)/(2(1+δ))) < K' D`. With
`δ = min(ε, 1/10)/3` that exponent is at least `1/2 − ε`.
-/

namespace Implications.Abc.Hall

open Real

/-- Copied verbatim from `FormalConjectures/Wikipedia/Hall.lean`, `Hall.HallIneq`. -/
def HallIneq (C : ℝ) (e : ℝ) : Prop :=
  ∀ x y : ℤ, y ^ 2 ≠ x ^ 3 → |y ^ 2 - x ^ 3| > C * (|x| : ℝ) ^ e

/-- Copied verbatim from `FormalConjectures/Wikipedia/Hall.lean`, `Hall.HallConjectureExp`. -/
def HallConjectureExp (e : ℝ) : Prop := ∃ C : ℝ, C > 0 ∧ HallIneq C e

/-- `Hall.weak_hall_conjecture` (`FormalConjectures/Wikipedia/Hall.lean`), statement verbatim:
Weak form of Hall's conjecture: relax the exponent from $1/2$ to $1/2 - \varepsilon$. -/
def WeakHallConjecture : Prop :=
  ∀ (ε : ℝ) (hε : ε > 0), HallConjectureExp (2⁻¹ - ε)

/-- `(XY)^6 ≤ M^5` when `X³ ≤ M` and `Y² ≤ M`. -/
lemma mul_pow_six_le {X Y M : ℕ} (hX : X ^ 3 ≤ M) (hY : Y ^ 2 ≤ M) : (X * Y) ^ 6 ≤ M ^ 5 := by
  calc (X * Y) ^ 6 = (X ^ 3) ^ 2 * (Y ^ 2) ^ 3 := by ring
    _ ≤ M ^ 2 * M ^ 3 := by gcongr
    _ = M ^ 5 := by ring

/-- The main estimate for `x > 0`: abc gives `X^e < K' D` for some `K' > 0`. -/
lemma main_bound (hK : ABCConstantMul) {ε : ℝ} (hε : 0 < ε) :
    ∃ K' : ℝ, 0 < K' ∧ ∀ X Y D : ℕ, 0 < X → 0 < Y → 0 < D →
      (Y ^ 2 + D = X ^ 3 ∨ X ^ 3 + D = Y ^ 2) → (X : ℝ) ^ (2⁻¹ - ε) < K' * D := by
  set δ : ℝ := min ε (1 / 10) / 3 with hδdef
  have hδ0 : 0 < δ := by positivity
  have hδε : 3 * δ ≤ ε := by
    have := min_le_left ε (1 / 10); rw [hδdef]; linarith
  have hδ10 : 3 * δ ≤ 1 / 10 := by
    have := min_le_right ε (1 / 10); rw [hδdef]; linarith
  obtain ⟨K, hK⟩ := hK δ hδ0
  -- K > 0 from the triple (1, 1, 2)
  have hK0 : 0 < K := by
    have h := hK 1 1 2 one_pos one_pos two_pos
      (pairwise_coprime_triple (Nat.coprime_one_left _) (Nat.coprime_one_left _)
        (Nat.coprime_one_left _)) rfl
    by_contra hK0
    push Not at hK0
    have : K * ((radical (1 * 1 * 2) : ℕ) : ℝ) ^ (1 + δ) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg hK0 (Real.rpow_nonneg (Nat.cast_nonneg _) _)
    push_cast at h
    linarith
  refine ⟨K ^ (1 + δ)⁻¹, Real.rpow_pos_of_pos hK0 _, fun X Y D hX hY hD hsum => ?_⟩
  -- `M < K (X Y D)^(1+δ)` with `X³ ≤ M`, `Y² ≤ M`
  obtain ⟨M, hXM, hYM, hM⟩ : ∃ M : ℕ, X ^ 3 ≤ M ∧ Y ^ 2 ≤ M ∧
      (M : ℝ) < K * ((X * Y : ℕ) * (D : ℝ)) ^ (1 + δ) := by
    rcases hsum with h | h
    · refine ⟨X ^ 3, le_rfl, by omega, ?_⟩
      have := lt_of_constantMul hK hδ0 (A := Y ^ 2) (B := D) (P := Y) (Q := X)
        (by positivity) hD (by rw [radical_pow two_ne_zero]; exact radical_le_self (by omega))
        (by rw [h, radical_pow three_ne_zero]; exact radical_le_self (by omega))
      rw [h] at this
      convert this using 3; push_cast; ring
    · refine ⟨Y ^ 2, by omega, le_rfl, ?_⟩
      have := lt_of_constantMul hK hδ0 (A := X ^ 3) (B := D) (P := X) (Q := Y)
        (by positivity) hD (by rw [radical_pow three_ne_zero]; exact radical_le_self (by omega))
        (by rw [h, radical_pow two_ne_zero]; exact radical_le_self (by omega))
      rw [h] at this
      convert this using 3; push_cast; ring
  have hM1 : (1 : ℝ) ≤ M := by
    have : 1 ≤ M := le_trans (Nat.one_le_pow _ _ hX) hXM
    exact_mod_cast this
  have h6 : (((X * Y : ℕ) : ℝ)) ^ 6 ≤ (M : ℝ) ^ 5 := by
    exact_mod_cast mul_pow_six_le hXM hYM
  have hu := rpow_lt_of_sixth hM1 (Nat.cast_nonneg _) (Nat.cast_nonneg D) hδ0 h6 hM
  set u : ℝ := (1 - 5 * δ) / 6 with hudef
  have hu0 : 0 < u := by rw [hudef]; linarith
  have hX1 : (1 : ℝ) ≤ X := by exact_mod_cast hX
  have hX0 : (0 : ℝ) ≤ X := by linarith
  -- `X^(3u) ≤ M^u`
  have h3 : (X : ℝ) ^ (3 * u) ≤ (M : ℝ) ^ u := by
    rw [Real.rpow_mul hX0]
    have : ((X : ℝ) ^ (3 : ℝ)) ≤ M := by
      rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
      exact_mod_cast hXM
    exact Real.rpow_le_rpow (by positivity) this hu0.le
  have h4 : (X : ℝ) ^ (3 * u) < K * (D : ℝ) ^ (1 + δ) := h3.trans_lt hu
  have hδ1 : 0 < 1 + δ := by linarith
  -- raise to the power `1/(1+δ)`
  have h5 : ((X : ℝ) ^ (3 * u)) ^ (1 + δ)⁻¹ < (K * (D : ℝ) ^ (1 + δ)) ^ (1 + δ)⁻¹ :=
    Real.rpow_lt_rpow (by positivity) h4 (by positivity)
  rw [← Real.rpow_mul hX0, Real.mul_rpow hK0.le (by positivity), ← Real.rpow_mul
    (Nat.cast_nonneg D), mul_inv_cancel₀ hδ1.ne', Real.rpow_one] at h5
  refine lt_of_le_of_lt ?_ h5
  apply Real.rpow_le_rpow_of_exponent_le hX1
  rw [hudef, ← div_eq_mul_inv, le_div_iff₀ hδ1]
  nlinarith

/-- The easy case: `X ≤ D` and `1 ≤ D`. -/
lemma easy {X D : ℕ} {e : ℝ} (he : e ≤ 1) (hD : 1 ≤ D) (hXD : X ≤ D) :
    (2⁻¹ : ℝ) * (X : ℝ) ^ e < D := by
  have hD1 : (1 : ℝ) ≤ D := by exact_mod_cast hD
  have hle : (X : ℝ) ^ e ≤ D := by
    rcases Nat.eq_zero_or_pos X with rfl | hX
    · simpa using (Real.zero_rpow_le_one e).trans hD1
    · have hX1 : (1 : ℝ) ≤ X := by exact_mod_cast hX
      calc (X : ℝ) ^ e ≤ (X : ℝ) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hX1 he
        _ = X := Real.rpow_one _
        _ ≤ D := by exact_mod_cast hXD
  linarith

/-- **abc implies the weak Hall conjecture** (`Hall.weak_hall_conjecture`). -/
theorem weakHall_of_abcConstantMul (hK : ABCConstantMul) : WeakHallConjecture := by
  intro ε hε
  obtain ⟨K', hK'0, hK'⟩ := main_bound hK hε
  refine ⟨min 2⁻¹ K'⁻¹, lt_min (by norm_num) (inv_pos.2 hK'0), fun x y hxy => ?_⟩
  set D : ℕ := (y ^ 2 - x ^ 3).natAbs with hDdef
  set X : ℕ := x.natAbs
  have hD1 : 1 ≤ D := Int.natAbs_pos.2 (sub_ne_zero.2 hxy)
  have hDcast : ((|y ^ 2 - x ^ 3| : ℤ) : ℝ) = (D : ℝ) := by
    rw [hDdef, Int.cast_abs]; push_cast; rfl
  have hXcast : (|(x : ℝ)|) = (X : ℝ) := by
    rw [Nat.cast_natAbs, Int.cast_abs]
  have he : (2⁻¹ - ε : ℝ) ≤ 1 := by linarith
  have hCnn : 0 ≤ min 2⁻¹ K'⁻¹ := le_min (by norm_num) (inv_pos.2 hK'0).le
  have hXe : (0 : ℝ) ≤ (X : ℝ) ^ (2⁻¹ - ε) := Real.rpow_nonneg (Nat.cast_nonneg _) _
  show _ < _
  rw [hXcast]
  push_cast at hDcast ⊢
  rw [hDcast]
  by_cases hXD : X ≤ D
  · calc min 2⁻¹ K'⁻¹ * (X : ℝ) ^ (2⁻¹ - ε) ≤ 2⁻¹ * (X : ℝ) ^ (2⁻¹ - ε) := by
          gcongr; exact min_le_left _ _
      _ < D := easy he hD1 hXD
  push Not at hXD
  -- now `x > 0` and `y ≠ 0`
  have hx : 0 < x := by
    by_contra hx
    push Not at hx
    have : (X : ℤ) ≤ (D : ℤ) := by
      rw [hDdef, Int.natCast_natAbs, Int.natCast_natAbs, abs_of_nonpos hx]
      have h1 : y ^ 2 - x ^ 3 = y ^ 2 + (-x) ^ 3 := by ring
      have h2 : (0 : ℤ) ≤ y ^ 2 := sq_nonneg y
      have h3 : -x ≤ (-x) ^ 3 := by
        rcases eq_or_lt_of_le hx with h | h
        · subst h; simp
        · nlinarith [sq_nonneg (-x)]
      rw [h1, abs_of_nonneg (by nlinarith)]
      linarith
    omega
  set Y : ℕ := y.natAbs
  have hXx : (X : ℤ) = x := by simp [X, abs_of_pos hx]
  have hYy : (Y : ℤ) ^ 2 = y ^ 2 := by simp [Y]
  have hY : 0 < Y := by
    by_contra hY
    have hY0 : Y = 0 := by omega
    have : (D : ℤ) = (X : ℤ) ^ 3 := by
      rw [hDdef, Int.natCast_natAbs, ← hYy, hY0, hXx]
      simp [abs_of_pos (pow_pos hx 3)]
    have : D = X ^ 3 := by exact_mod_cast this
    have : X ≤ X ^ 3 := Nat.le_self_pow (by norm_num) X
    omega
  have hsum : Y ^ 2 + D = X ^ 3 ∨ X ^ 3 + D = Y ^ 2 := by
    have hDz : (D : ℤ) = |(Y : ℤ) ^ 2 - (X : ℤ) ^ 3| := by
      rw [hDdef, Int.natCast_natAbs, hYy, hXx]
    rcases le_total ((Y : ℤ) ^ 2) ((X : ℤ) ^ 3) with h | h
    · left
      rw [abs_of_nonpos (by linarith)] at hDz
      have : ((Y ^ 2 + D : ℕ) : ℤ) = ((X ^ 3 : ℕ) : ℤ) := by push_cast; linarith
      exact_mod_cast this
    · right
      rw [abs_of_nonneg (by linarith)] at hDz
      have : ((X ^ 3 + D : ℕ) : ℤ) = ((Y ^ 2 : ℕ) : ℤ) := by push_cast; linarith
      exact_mod_cast this
  have hmain := hK' X Y D (by omega) hY (by omega) hsum
  calc min 2⁻¹ K'⁻¹ * (X : ℝ) ^ (2⁻¹ - ε) ≤ K'⁻¹ * (X : ℝ) ^ (2⁻¹ - ε) := by
        gcongr; exact min_le_right _ _
    _ < K'⁻¹ * (K' * D) := by gcongr
    _ = D := by field_simp

/-- **abc implies the weak Hall conjecture**, from `ABC.abc` itself. -/
theorem weakHall_of_abc (habc : ABCConjecture) : WeakHallConjecture :=
  weakHall_of_abcConstantMul (abcConstantMul_of_abc habc)

end Implications.Abc.Hall
