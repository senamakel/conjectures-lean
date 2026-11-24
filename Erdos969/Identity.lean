import Erdos969.Statement

/-!
# The Möbius identity for squarefree numbers

`Q(N) = ∑_{d ≤ N} μ(d) ⌊N / d²⌋`, from `∑_{d² ∣ n} μ(d) = 1` if `n` is squarefree and `0` otherwise.
-/

namespace Erdos969

open Finset ArithmeticFunction
open scoped ArithmeticFunction.Moebius

lemma sq_dvd_iff {a b d : ℕ} (ha : Squarefree a) (hb : 0 < b) :
    d * d ∣ b ^ 2 * a ↔ d ∣ b := by
  constructor
  · intro h
    rcases Nat.eq_zero_or_pos d with rfl | hd
    · exfalso
      have ha0 : 0 < a := Nat.pos_of_ne_zero ha.ne_zero
      rw [zero_mul, zero_dvd_iff] at h
      exact (by positivity : b ^ 2 * a ≠ 0) h
    · obtain ⟨d', b', hco, hd', hb'⟩ := Nat.exists_coprime d b
      have hg : 0 < Nat.gcd d b := Nat.gcd_pos_of_pos_left _ hd
      set g := Nat.gcd d b
      have h2 : g ^ 2 * (d' * d') ∣ g ^ 2 * (b' ^ 2 * a) := by
        have e1 : d * d = g ^ 2 * (d' * d') := by rw [hd']; ring
        have e2 : b ^ 2 * a = g ^ 2 * (b' ^ 2 * a) := by rw [hb']; ring
        rw [← e1, ← e2]; exact h
      have h3 : d' * d' ∣ b' ^ 2 * a := (Nat.mul_dvd_mul_iff_left (by positivity)).1 h2
      have hc : Nat.Coprime (d' * d') (b' ^ 2) := by
        have := (Nat.Coprime.pow 2 2 hco)
        simpa [pow_two] using this
      have h4 : d' * d' ∣ a := hc.dvd_of_dvd_mul_left h3
      have h5 : IsUnit d' := ha _ h4
      have : d' = 1 := Nat.isUnit_iff.1 h5
      subst this
      exact ⟨b', by rw [hb', hd']; ring⟩
  · intro h
    exact (Nat.mul_dvd_mul h h).trans ⟨a, by ring⟩

lemma sum_moebius_sq_dvd {n : ℕ} (hn : 0 < n) :
    ∑ d ∈ (Icc 1 n).filter (fun d => d * d ∣ n), (μ d : ℤ) = if Squarefree n then 1 else 0 := by
  obtain ⟨a, b, ha0, hb0, hab, hsq⟩ := Nat.sq_mul_squarefree_of_pos hn
  subst hab
  have hset : (Icc 1 (b ^ 2 * a)).filter (fun d => d * d ∣ b ^ 2 * a) = b.divisors := by
    ext d
    simp only [mem_filter, mem_Icc, Nat.mem_divisors, sq_dvd_iff hsq hb0]
    constructor
    · rintro ⟨_, h⟩; exact ⟨h, hb0.ne'⟩
    · rintro ⟨h, _⟩
      refine ⟨⟨Nat.pos_of_dvd_of_pos h hb0, ?_⟩, h⟩
      calc d ≤ b := Nat.le_of_dvd hb0 h
        _ ≤ b ^ 2 * a := by nlinarith
  rw [hset]
  have h1 : ∑ d ∈ b.divisors, (μ d : ℤ) = if b = 1 then 1 else 0 := by
    have h := congrArg (fun f : ArithmeticFunction ℤ => f b) (moebius_mul_coe_zeta)
    simp only [coe_mul_zeta_apply] at h
    rw [h]
    rfl
  rw [h1]
  by_cases hb : b = 1
  · subst hb; simp [hsq]
  · have : ¬ Squarefree (b ^ 2 * a) := by
      intro h
      have h' : b * b ∣ b ^ 2 * a := ⟨a, by ring⟩
      exact hb (Nat.isUnit_iff.1 (h _ h'))
    simp [hb, this]

/-- `Q(N) = ∑_{d ≤ N} μ(d) ⌊N / d²⌋`. -/
theorem squarefreeCounting_eq (N : ℕ) :
    (squarefreeCounting N : ℤ) = ∑ d ∈ Icc 1 N, (μ d : ℤ) * ((N / (d * d) : ℕ) : ℤ) := by
  have h1 : (squarefreeCounting N : ℤ) =
      ∑ n ∈ Icc 1 N, ∑ d ∈ (Icc 1 n).filter (fun d => d * d ∣ n), (μ d : ℤ) := by
    unfold squarefreeCounting
    rw [Finset.card_filter, Nat.cast_sum]
    refine sum_congr rfl fun n hn => ?_
    rw [sum_moebius_sq_dvd (mem_Icc.1 hn).1]
    split_ifs <;> simp
  rw [h1]
  have h2 : ∀ n ∈ Icc 1 N, ∑ d ∈ (Icc 1 n).filter (fun d => d * d ∣ n), (μ d : ℤ) =
      ∑ d ∈ Icc 1 N, if d * d ∣ n then (μ d : ℤ) else 0 := by
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
      nlinarith
  rw [sum_congr rfl h2, sum_comm]
  refine sum_congr rfl fun d hd => ?_
  rw [← sum_filter, sum_const, nsmul_eq_mul, mul_comm]
  congr 2
  have : ((Icc 1 N).filter (fun n => d * d ∣ n)) = (Ioc 0 N).filter (fun n => d * d ∣ n) := by
    ext n; simp only [mem_filter, mem_Icc, mem_Ioc]; omega
  rw [this, Nat.Ioc_filter_dvd_card_eq_div]

end Erdos969
