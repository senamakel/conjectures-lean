import Implications.ABC.Variants

/-!
# abc for triples that are not coprime, and a real-exponent bound

Toolkit for `Implications.ABC.Hall` and `Implications.ABC.Pillai`.

* `lt_of_constantMul`: the constant form of abc (`ABC.ABCConstantMul`) applied to `A + B = C`
  after dividing out `g = gcd(A, B)`. If `rad A ≤ P` and `rad (A + B) ≤ Q` then
  `A + B < K (P Q B)^(1+ε)`. The factor `g` lost by the division is absorbed because `g ∣ B` and
  the bound keeps `B` itself, not `rad B`.
* `rpow_lt_of_sixth`: from `m < K (p d)^(1+δ)` and `p^6 ≤ m^5` (which is how `1/m + 1/n ≤ 5/6`
  enters), `m^((1-5δ)/6) < K d^(1+δ)`.
-/

namespace Implications.Abc

open _root_.ABC

lemma radical_le_self {n : ℕ} (hn : n ≠ 0) : radical n ≤ n :=
  Nat.le_of_dvd (Nat.pos_of_ne_zero hn) (Nat.prod_primeFactors_dvd n)

lemma radical_dvd_radical {m n : ℕ} (h : m ∣ n) (hn : n ≠ 0) : radical m ∣ radical n :=
  Finset.prod_dvd_prod_of_subset _ _ _ (Nat.primeFactors_mono h hn)

lemma radical_le_radical {m n : ℕ} (h : m ∣ n) (hn : n ≠ 0) : radical m ≤ radical n :=
  Nat.le_of_dvd (radical_pos _) (radical_dvd_radical h hn)

/-- The constant form of abc for a triple that need not be coprime. -/
lemma lt_of_constantMul {ε K : ℝ}
    (hK : ∀ (a b c : ℕ), 0 < a → 0 < b → 0 < c → ({a, b, c} : Set ℕ).Pairwise Nat.Coprime →
      a + b = c → c < K * (radical <| a * b * c : ℝ)^(1 + ε))
    (hε : 0 < ε) {A B P Q : ℕ} (hA : 0 < A) (hB : 0 < B)
    (hP : radical A ≤ P) (hQ : radical (A + B) ≤ Q) :
    ((A + B : ℕ) : ℝ) < K * ((P * Q * B : ℕ) : ℝ) ^ (1 + ε) := by
  set g := Nat.gcd A B with hg
  have hg0 : 0 < g := Nat.gcd_pos_of_pos_left _ hA
  set A' := A / g
  set B' := B / g
  have hAe : A = g * A' := (Nat.mul_div_cancel' (Nat.gcd_dvd_left A B)).symm
  have hBe : B = g * B' := (Nat.mul_div_cancel' (Nat.gcd_dvd_right A B)).symm
  have hA' : 0 < A' := Nat.div_pos (Nat.le_of_dvd hA (Nat.gcd_dvd_left A B)) hg0
  have hB' : 0 < B' := Nat.div_pos (Nat.le_of_dvd hB (Nat.gcd_dvd_right A B)) hg0
  have hcop : Nat.Coprime A' B' := Nat.coprime_div_gcd_div_gcd hg0
  have hcop1 : Nat.Coprime A' (A' + B') := Nat.coprime_self_add_right.2 hcop
  have hcop2 : Nat.Coprime B' (A' + B') := Nat.coprime_add_self_right.2 hcop.symm
  have hsum : A + B = g * (A' + B') := by rw [hAe, hBe]; ring
  have h := hK A' B' (A' + B') hA' hB' (by omega) (pairwise_coprime_triple hcop hcop1 hcop2) rfl
  -- bound the radical
  have hR : radical (A' * B' * (A' + B')) ≤ P * B' * Q := by
    calc radical (A' * B' * (A' + B'))
        ≤ radical (A' * B') * radical (A' + B') := radical_mul_le (by positivity) (by omega)
      _ ≤ radical A' * radical B' * radical (A' + B') :=
          Nat.mul_le_mul_right _ (radical_mul_le (by omega) (by omega))
      _ ≤ P * B' * Q := by
          gcongr
          · exact (radical_le_radical ⟨g, by rw [hAe]; ring⟩ (by omega)).trans hP
          · exact radical_le_self (by omega)
          · exact (radical_le_radical ⟨g, by rw [hsum]; ring⟩ (by omega)).trans hQ
  have hRr : ((radical (A' * B' * (A' + B')) : ℕ) : ℝ) ≤ ((P * B' * Q : ℕ) : ℝ) := by
    exact_mod_cast hR
  have hr0 : (0 : ℝ) ≤ ((radical (A' * B' * (A' + B')) : ℕ) : ℝ) := Nat.cast_nonneg _
  have hpos : (0 : ℝ) < ((A' + B' : ℕ) : ℝ) := by exact_mod_cast (show 0 < A' + B' by omega)
  have hK0 : 0 < K := by
    by_contra hK0
    push Not at hK0
    have : K * ((radical (A' * B' * (A' + B')) : ℕ) : ℝ) ^ (1 + ε) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg hK0 (Real.rpow_nonneg hr0 _)
    linarith
  have hg1 : (1 : ℝ) ≤ g := by exact_mod_cast hg0
  have hgpow : (g : ℝ) ≤ (g : ℝ) ^ (1 + ε) := by
    calc (g : ℝ) = (g : ℝ) ^ (1 : ℝ) := (Real.rpow_one _).symm
      _ ≤ (g : ℝ) ^ (1 + ε) := Real.rpow_le_rpow_of_exponent_le hg1 (by linarith)
  have hPQB : ((P * Q * B : ℕ) : ℝ) = (g : ℝ) * ((P * B' * Q : ℕ) : ℝ) := by
    rw [hBe]; push_cast; ring
  have hmono : ((radical (A' * B' * (A' + B')) : ℕ) : ℝ) ^ (1 + ε) ≤
      ((P * B' * Q : ℕ) : ℝ) ^ (1 + ε) := Real.rpow_le_rpow hr0 hRr (by linarith)
  have hX0 : (0 : ℝ) ≤ ((P * B' * Q : ℕ) : ℝ) := Nat.cast_nonneg _
  calc ((A + B : ℕ) : ℝ) = (g : ℝ) * ((A' + B' : ℕ) : ℝ) := by rw [hsum]; push_cast; ring
    _ < (g : ℝ) * (K * ((radical (A' * B' * (A' + B')) : ℕ) : ℝ) ^ (1 + ε)) :=
        mul_lt_mul_of_pos_left h (by linarith)
    _ ≤ (g : ℝ) * (K * ((P * B' * Q : ℕ) : ℝ) ^ (1 + ε)) := by gcongr
    _ = K * ((g : ℝ) * ((P * B' * Q : ℕ) : ℝ) ^ (1 + ε)) := by ring
    _ ≤ K * ((g : ℝ) ^ (1 + ε) * ((P * B' * Q : ℕ) : ℝ) ^ (1 + ε)) := by
        gcongr
    _ = K * ((P * Q * B : ℕ) : ℝ) ^ (1 + ε) := by
        rw [hPQB, Real.mul_rpow (by linarith) hX0]

/-- From `m < K (p d)^(1+δ)` and `p^6 ≤ m^5`, `m^((1-5δ)/6) < K d^(1+δ)`. -/
lemma rpow_lt_of_sixth {m p d K δ : ℝ} (hm : 1 ≤ m) (hp : 0 ≤ p) (hd : 0 ≤ d) (hδ : 0 < δ)
    (hpm : p ^ 6 ≤ m ^ 5) (h : m < K * (p * d) ^ (1 + δ)) :
    m ^ ((1 - 5 * δ) / 6) < K * d ^ (1 + δ) := by
  have hm0 : 0 < m := by linarith
  have hK0 : 0 < K := by
    by_contra hK0
    push Not at hK0
    have : K * (p * d) ^ (1 + δ) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg hK0 (Real.rpow_nonneg (mul_nonneg hp hd) _)
    linarith
  -- `p ≤ m^(5/6)`
  have hp56 : p ≤ m ^ ((5 : ℝ) / 6) := by
    have h1 : (p ^ 6) ^ ((6 : ℕ)⁻¹ : ℝ) ≤ (m ^ 5) ^ ((6 : ℕ)⁻¹ : ℝ) :=
      Real.rpow_le_rpow (by positivity) hpm (by positivity)
    rw [Real.pow_rpow_inv_natCast hp (by norm_num), ← Real.rpow_natCast,
      ← Real.rpow_mul hm0.le] at h1
    convert h1 using 2
    norm_num
  have hpow : p ^ (1 + δ) ≤ m ^ ((5 : ℝ) / 6 * (1 + δ)) := by
    rw [Real.rpow_mul hm0.le]
    exact Real.rpow_le_rpow hp hp56 (by linarith)
  have hv : 0 < m ^ ((5 : ℝ) / 6 * (1 + δ)) := Real.rpow_pos_of_pos hm0 _
  have hsplit : m = m ^ ((1 - 5 * δ) / 6) * m ^ ((5 : ℝ) / 6 * (1 + δ)) := by
    rw [← Real.rpow_add hm0]
    conv_lhs => rw [← Real.rpow_one m]
    congr 1; ring
  have hd' : 0 ≤ d ^ (1 + δ) := Real.rpow_nonneg hd _
  have h2 : m ^ ((1 - 5 * δ) / 6) * m ^ ((5 : ℝ) / 6 * (1 + δ)) <
      (K * d ^ (1 + δ)) * m ^ ((5 : ℝ) / 6 * (1 + δ)) := by
    rw [← hsplit]
    calc m < K * (p * d) ^ (1 + δ) := h
      _ = K * (p ^ (1 + δ) * d ^ (1 + δ)) := by rw [Real.mul_rpow hp hd]
      _ ≤ K * (m ^ ((5 : ℝ) / 6 * (1 + δ)) * d ^ (1 + δ)) := by gcongr
      _ = (K * d ^ (1 + δ)) * m ^ ((5 : ℝ) / 6 * (1 + δ)) := by ring
  exact lt_of_mul_lt_mul_right h2 hv.le

end Implications.Abc
