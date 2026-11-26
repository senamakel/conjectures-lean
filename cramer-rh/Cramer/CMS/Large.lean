import Cramer.CMS.Final

/-!
# The analytic range `x ≥ 10⁸` of the Carneiro–Milinovich–Soundararajan interval

Suppose `(x, x + (22/25)√x log x]` has no prime. Put `s' = ⌊(q − 2)/128⌋` with
`q = (22/25)√x log x` and `B = ⌊x⌋ + 1 − 64 s'`, and take the CMS weight with knots
`n_j = B + 8 s' j`, `j = 0, …, 32`; its gap `[n_8, n_24)` lies inside the interval. Then

* the explicit formula and the zero sum (`sum_psi1N_ge_of_zeroSum`, `zeroBound`) give
  `Σ Λ(n) w(n) ≥ s² Σ c_j − s² m^{−1/2} Zc(s/m) − (3/2) Σ |a_j|`, with `s = 8 s'`;
* Brun–Titchmarsh (`sum_Lambda_wt_le`) gives
  `Σ Λ(n) w(n) ≤ s'² log n_32 · 18838744 / W + s' · 8388608 · PP`, since no prime lies in the
  gap;

and the two contradict `final_ineq`.
-/

namespace Cramer.CMS

open Finset Real ArithmeticFunction
open Schoenfeld (Zeros mult)

/-- **Under RH, `(x, x + (22/25)√x log x]` contains a prime for every `x ≥ 10⁸`.** -/
theorem exists_prime_large_cms (hRH : RiemannHypothesis) {x : ℝ} (hx : 1e8 ≤ x) :
    ∃ p : ℕ, p.Prime ∧ x < p ∧ (p : ℝ) ≤ x + 22 / 25 * √x * Real.log x := by
  by_contra hno
  push_neg at hno
  obtain ⟨hu4, ht, hu29, hc, hlu⟩ := growth hx
  have hx0 : 0 < x := by linarith
  have hux : √x ^ 2 = x := Real.sq_sqrt hx0.le
  set u := √x with hu
  set t := Real.log x with htdef
  have hu0 : 0 < u := by linarith
  have ht0 : 0 < t := by linarith
  set q := 22 / 25 * u * t with hq
  have hq0 : 158400 ≤ q := by nlinarith
  have hqx : q / 2 + 1 ≤ x := by
    rw [← hux]; nlinarith
  -- the piece length
  set s' := ⌊(q - 2) / 128⌋₊ with hs'
  have hs'1 : (s' : ℝ) ≤ (q - 2) / 128 := Nat.floor_le (by linarith)
  have hs'2 : (q - 2) / 128 - 1 < s' := Nat.sub_one_lt_floor _
  have hs'pos : 1 ≤ s' := by
    have : (1 : ℝ) ≤ s' := by linarith
    exact_mod_cast this
  -- the knots
  set N0 := ⌊x⌋₊ with hN0
  have hN1 : (N0 : ℝ) ≤ x := Nat.floor_le hx0.le
  have hN2 : x < N0 + 1 := Nat.lt_floor_add_one x
  have h320 : 320 * s' ≤ N0 + 1 := by
    have : (320 * s' : ℝ) ≤ N0 + 1 := by nlinarith
    exact_mod_cast this
  set B := N0 + 1 - 64 * s' with hB
  have hBe : B + 64 * s' = N0 + 1 := by omega
  have hBr : (B : ℝ) = N0 + 1 - 64 * s' := by
    have : ((B + 64 * s' : ℕ) : ℝ) = N0 + 1 := by rw [hBe]; push_cast; ring
    push_cast at this; linarith
  set y : ℝ := (s' : ℝ) with hydef
  set m : ℝ := (B : ℝ) + 128 * (s' : ℝ) with hm
  have S : Setting u t y m :=
    { hu4 := hu4, ht := ht, hu29 := hu29, hlu := by rw [hlu],
      hy1 := by linarith, hy2 := by linarith,
      hm1 := by rw [hux, hm, hBr]; linarith,
      hm2 := by rw [hux, hm, hBr]; linarith }
  have hy0 := S.y_pos
  have hm0 := S.m_pos
  -- the zero side
  have hsmall : 8 * y / m ≤ 1 / 64 := by
    refine S.h_le'.trans ?_
    rw [div_le_iff₀ ht0]; linarith
  obtain ⟨hsum, hZ⟩ := zeroBound hRH hm0 (by positivity : (0 : ℝ) < 8 * y) hsmall
  have htk : ∀ j : ℕ, tk m (8 * y) 16 j = ((kn B (8 * s') j : ℕ) : ℝ) := by
    intro j; simp only [tk, kn, hm, y]; push_cast; ring
  simp only [htk] at hsum hZ
  have hB1 : 1 ≤ B := by omega
  have hlow := sum_psi1N_ge_of_zeroSum hRH cdat cdat_zero cdat_high hB1 hsum hZ
  have hA : ∑ j ∈ range (2 * 16 + 1), |(aco cdat j : ℝ)| = 740648 := by
    have h := Asum_val
    unfold Asum at h
    have : ((∑ j ∈ range (2 * 16 + 1), (aco cdat j).natAbs : ℕ) : ℝ) = 740648 := by
      rw [h]; norm_num
    rw [← this]; push_cast
    refine sum_congr rfl fun j _ => ?_
    rw [Nat.cast_natAbs, Int.cast_abs]
  have hC : ∑ j ∈ range (2 * 16 + 1), (cdat j : ℝ) = 11989718 := by
    have h := sum_cdat
    have : ((∑ j ∈ range (2 * 16 + 1), cdat j : ℤ) : ℝ) = 11989718 := by rw [h]; norm_num
    rw [← this]; push_cast; rfl
  rw [hA, hC] at hlow
  have hcast : ((8 * s' : ℕ) : ℝ) = 8 * y := by push_cast; rfl
  rw [hcast] at hlow
  -- `Σ Λ(n) w(n) = Σ a_j Ψ₁(n_j)`
  have hid := sum_vonMangoldt_wt cdat 32 B (8 * s') (kn B (8 * s') 32 + 1) (by
    intro j hj; simp only [mem_range] at hj; simp only [kn]
    have : j * (8 * s') ≤ 32 * (8 * s') := Nat.mul_le_mul_right _ (by omega)
    omega)
  -- the prime side
  have hW := S.W_lower
  have hnop : ∀ p : ℕ, p.Prime → kn B (8 * s') 8 ≤ p → p < kn B (8 * s') 24 → False := by
    intro p hp h1 h2
    have h1' : (N0 + 1 : ℝ) ≤ p := by
      have : N0 + 1 ≤ p := by simp only [kn] at h1; omega
      exact_mod_cast this
    have h2' : (p : ℝ) ≤ N0 + 128 * s' := by
      have : p ≤ N0 + 128 * s' := by simp only [kn] at h2; omega
      exact_mod_cast this
    have := hno p hp (by linarith)
    linarith
  have hR : Real.sqrt (2 * ((s' : ℕ) : ℝ) / 3) + 1 ≤ (B : ℝ) := by
    have h1 : Real.sqrt (2 * (s' : ℝ) / 3) ≤ s' := by
      rw [Real.sqrt_le_left (by positivity)]
      have : (1 : ℝ) ≤ s' := by exact_mod_cast hs'pos
      nlinarith
    have h2 : (s' : ℝ) + 1 ≤ B := by
      have : s' + 1 ≤ B := by omega
      exact_mod_cast this
    linarith
  have hupper := sum_Lambda_wt_le hs'pos hB1 (by simp only [kn]; omega) hR
    (by linarith [S.ht]) hnop
  rw [hid] at hupper
  -- the contradiction
  have hfin := S.final_ineq hc (a := (kn B (8 * s') 0 : ℝ)) (b := (kn B (8 * s') 32 : ℝ))
    (by simp only [kn]; push_cast; rw [hux, hBr]; linarith)
    (by simp only [kn]; push_cast; rw [hux, hBr]; linarith)
    (by simp only [kn]; push_cast; ring)
  have hPP : PPb (kn B (8 * s') 0) (kn B (8 * s') 32) =
      PPr (kn B (8 * s') 0 : ℝ) (kn B (8 * s') 32 : ℝ) := rfl
  rw [hPP] at hupper
  linarith

end Cramer.CMS
