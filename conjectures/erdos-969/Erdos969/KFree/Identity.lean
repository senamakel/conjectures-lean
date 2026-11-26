import Erdos969.Statement
import Erdos969.Statement2

/-!
# The Möbius identity for `k`-free numbers

`Q_k(N) = ∑_{d ≤ N} μ(d) ⌊N / d^k⌋`, from `∑_{d^k ∣ n} μ(d) = [n is k-free]`. The `d` with
`d^k ∣ n` are exactly the divisors of `Nat.floorRoot k n` (Mathlib's `pow_dvd_iff_dvd_floorRoot`),
and `n` is `k`-free exactly when that root is `1`.

`kFreeCounting_two` and `kFreeCountingError_two` check that `k = 2` gives back the squarefree
definitions of `Erdos969/Statement.lean`.
-/

namespace Erdos969.KFree

open Finset ArithmeticFunction
open scoped ArithmeticFunction.Moebius

lemma powerfree_iff_floorRoot_eq_one {k n : ℕ} :
    Powerfree k n ↔ Nat.floorRoot k n = 1 := by
  constructor
  · intro h
    exact Nat.isUnit_iff.1 (h Nat.floorRoot_pow_dvd)
  · intro h x hx
    rw [Nat.pow_dvd_iff_dvd_floorRoot, h] at hx
    exact Nat.isUnit_iff.2 (Nat.dvd_one.1 hx)

lemma sum_moebius_pow_dvd {k n : ℕ} (hk : 1 ≤ k) (hn : 0 < n) :
    ∑ d ∈ (Icc 1 n).filter (fun d => d ^ k ∣ n), (μ d : ℤ) =
      if Nat.floorRoot k n = 1 then 1 else 0 := by
  set g := Nat.floorRoot k n with hg
  have hg0 : g ≠ 0 := Nat.floorRoot_ne_zero.2 ⟨by omega, by omega⟩
  have hgn : g ≤ n := by
    have h1 : g ^ k ∣ n := Nat.floorRoot_pow_dvd
    have h2 : g ≤ g ^ k := Nat.le_self_pow (by omega) g
    exact h2.trans (Nat.le_of_dvd hn h1)
  have hset : (Icc 1 n).filter (fun d => d ^ k ∣ n) = g.divisors := by
    ext d
    simp only [mem_filter, mem_Icc, Nat.mem_divisors, Nat.pow_dvd_iff_dvd_floorRoot, ← hg]
    constructor
    · rintro ⟨_, h⟩; exact ⟨h, hg0⟩
    · rintro ⟨h, _⟩
      exact ⟨⟨Nat.pos_of_dvd_of_pos h (Nat.pos_of_ne_zero hg0),
        (Nat.le_of_dvd (Nat.pos_of_ne_zero hg0) h).trans hgn⟩, h⟩
  rw [hset]
  have h := congrArg (fun f : ArithmeticFunction ℤ => f g) (moebius_mul_coe_zeta)
  simp only [coe_mul_zeta_apply] at h
  rw [h]
  rfl

/-- `Q_k(N) = ∑_{d ≤ N} μ(d) ⌊N / d^k⌋`. -/
theorem kFreeCounting_eq {k : ℕ} (hk : 1 ≤ k) (N : ℕ) :
    (kFreeCounting k N : ℤ) = ∑ d ∈ Icc 1 N, (μ d : ℤ) * ((N / d ^ k : ℕ) : ℤ) := by
  classical
  have h1 : (kFreeCounting k N : ℤ) =
      ∑ n ∈ Icc 1 N, ∑ d ∈ (Icc 1 n).filter (fun d => d ^ k ∣ n), (μ d : ℤ) := by
    unfold kFreeCounting
    rw [Finset.card_filter, Nat.cast_sum]
    refine sum_congr rfl fun n hn => ?_
    rw [sum_moebius_pow_dvd hk (mem_Icc.1 hn).1]
    by_cases h : Powerfree k n
    · simp [h, powerfree_iff_floorRoot_eq_one.1 h]
    · have h' : Nat.floorRoot k n ≠ 1 := fun h' => h (powerfree_iff_floorRoot_eq_one.2 h')
      simp [h, h']
  rw [h1]
  have h2 : ∀ n ∈ Icc 1 N, ∑ d ∈ (Icc 1 n).filter (fun d => d ^ k ∣ n), (μ d : ℤ) =
      ∑ d ∈ Icc 1 N, if d ^ k ∣ n then (μ d : ℤ) else 0 := by
    intro n hn
    rw [← sum_filter]
    refine sum_congr ?_ fun _ _ => rfl
    have hn' := mem_Icc.1 hn
    ext d
    simp only [mem_filter, mem_Icc]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨⟨h1, h2.trans hn'.2⟩, h3⟩
    · rintro ⟨⟨h1, _⟩, h3⟩
      refine ⟨⟨h1, ?_⟩, h3⟩
      have := Nat.le_of_dvd (by omega) h3
      exact (Nat.le_self_pow (by omega) d).trans this
  rw [sum_congr rfl h2, sum_comm]
  refine sum_congr rfl fun d hd => ?_
  rw [← sum_filter, sum_const, nsmul_eq_mul, mul_comm]
  congr 2
  have : ((Icc 1 N).filter (fun n => d ^ k ∣ n)) = (Ioc 0 N).filter (fun n => d ^ k ∣ n) := by
    ext n; simp only [mem_filter, mem_Icc, mem_Ioc]; omega
  rw [this, Nat.Ioc_filter_dvd_card_eq_div]

/-- At `k = 2` the `k`-free count is the squarefree count. -/
theorem kFreeCounting_two (x : ℕ) : kFreeCounting 2 x = squarefreeCounting x := by
  classical
  unfold kFreeCounting squarefreeCounting
  congr 1
  ext n
  simp only [mem_filter]
  refine and_congr Iff.rfl ⟨fun h y hy => h (by rwa [sq]), fun h y hy => h y (by rwa [← sq])⟩

/-- At `k = 2` the `k`-free error term is the squarefree error term (`ζ(2) = π²/6`). -/
theorem kFreeCountingError_two (x : ℕ) :
    kFreeCountingError 2 x = squarefreeCountingError x := by
  unfold kFreeCountingError squarefreeCountingError
  rw [kFreeCounting_two]
  have h : (riemannZeta ((2 : ℕ) : ℂ)).re = Real.pi ^ 2 / 6 := by
    rw [show ((2 : ℕ) : ℂ) = 2 by norm_num, riemannZeta_two]
    rw [show (Real.pi : ℂ) ^ 2 / 6 = ((Real.pi ^ 2 / 6 : ℝ) : ℂ) by push_cast; ring]
    exact Complex.ofReal_re _
  rw [h]
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  field_simp

end Erdos969.KFree
