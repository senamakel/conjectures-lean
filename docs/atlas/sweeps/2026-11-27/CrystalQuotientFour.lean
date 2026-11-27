import Mathlib

/-! The quotient-four branch of crystal component uniqueness. -/

namespace CrystalQuotientFour

theorem consecutive_squares {c b : ℕ} (hc : Odd c) (hb : Odd b)
    (hcb : c ≤ b) (h : (c+b)^2 = 4*((c+1)*(b+1))) :
    ∃ t : ℕ, c+1 = 2*t^2 ∧ b+1 = 2*(t+1)^2 := by
  obtain ⟨u, hu⟩ := hc
  obtain ⟨v, hv⟩ := hb
  have huv : u ≤ v := by omega
  obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le huv
  have hdif : b = c + 2*d := by omega
  have h' : ((c : ℤ)+(b : ℤ))^2 = 4*(((c : ℤ)+1)*(b+1)) := by exact_mod_cast h
  have hdif' : (b : ℤ) = (c : ℤ) + 2*d := by exact_mod_cast hdif
  have hd2' : (d : ℤ)^2 = (c : ℤ)+b+1 := by
    rw [hdif'] at h' ⊢
    nlinarith only [h']
  have hd2 : d^2 = c+b+1 := by exact_mod_cast hd2'
  have hodd : Odd (d^2) := by
    rw [hd2]
    exact ⟨u+v+1, by omega⟩
  have hoddd : Odd d := Nat.Odd.of_mul_left (by simpa only [pow_two] using hodd)
  obtain ⟨t, ht⟩ := hoddd
  have ht' : (d : ℤ) = 2*(t : ℤ)+1 := by exact_mod_cast ht
  refine ⟨t, ?_, ?_⟩
  · exact_mod_cast (show (c : ℤ)+1 = 2*(t : ℤ)^2 by
      rw [ht', hdif', ht'] at hd2'
      nlinarith only [hd2'])
  · exact_mod_cast (show (b : ℤ)+1 = 2*((t : ℤ)+1)^2 by
      rw [ht', hdif', ht'] at hd2'
      nlinarith only [hd2', hdif', ht'])

#print axioms consecutive_squares

theorem gcd_dvd_quotient {c b q : ℕ} (h : (c+b)^2 = q*((c+1)*(b+1))) :
    c.gcd b ∣ q := by
  have hc := Nat.gcd_dvd_left c b
  have hb := Nat.gcd_dvd_right c b
  have hs : c.gcd b ∣ (c+b)^2 := by
    rw [pow_two]
    exact dvd_mul_of_dvd_left (dvd_add hc hb) _
  have ht : c.gcd b ∣ q*c*b+q*c+q*b :=
    dvd_add (dvd_add (dvd_mul_of_dvd_left (dvd_mul_of_dvd_right hc _) _)
      (dvd_mul_of_dvd_right hc _)) (dvd_mul_of_dvd_right hb _)
  refine (Nat.dvd_add_iff_right ht).mpr ?_
  convert hs using 1
  rw [h]
  ring

theorem coprime_of_quotient_four {c b : ℕ} (hc : Odd c)
    (h : (c+b)^2 = 4*((c+1)*(b+1))) : c.Coprime b := by
  change c.gcd b = 1
  have hdvd := gcd_dvd_quotient h
  have hle : c.gcd b ≤ 4 := Nat.le_of_dvd (by decide) hdvd
  have hodd : Odd (c.gcd b) := by
    obtain ⟨k, hk⟩ := Nat.gcd_dvd_left c b
    exact Nat.Odd.of_mul_left (hk ▸ hc)
  interval_cases hval : c.gcd b <;> simp_all <;> obtain ⟨k, hk⟩ := hodd <;> omega

#print axioms coprime_of_quotient_four

theorem prime_mod_eight_of_twice_square {p n t : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hpd : p ∣ n) (ht : n+1 = 2*t^2) :
    p % 8 = 1 ∨ p % 8 = 7 := by
  have : Fact p.Prime := ⟨hp⟩
  have hn : (n : ZMod p) = 0 := by
    obtain ⟨k,rfl⟩ := hpd
    simp
  have htz : (n : ZMod p)+1 = 2*(t : ZMod p)^2 := by
    simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_pow, Nat.cast_one, Nat.cast_ofNat] using
      congrArg (fun k : ℕ => (k : ZMod p)) ht
  rw [hn,zero_add] at htz
  apply (ZMod.exists_sq_eq_two_iff hp2).mp
  refine ⟨2*(t : ZMod p), ?_⟩
  linear_combination 2*htz

theorem prime_mod_eight_of_quotient_four {a b p : ℕ}
    (ha : Odd a) (hb : Odd b) (hab : a ≤ b)
    (hq : (a+b)^2 = 4*((a+1)*(b+1)))
    (hp : p.Prime) (hpd : p ∣ a ∨ p ∣ b) :
    p % 8 = 1 ∨ p % 8 = 7 := by
  obtain ⟨t,hta,htb⟩ := consecutive_squares ha hb hab hq
  have hp2 : p ≠ 2 := by
    intro he
    subst p
    rcases hpd with hd | hd
    · obtain ⟨j,hj⟩ := hd
      obtain ⟨k,hk⟩ := ha
      omega
    · obtain ⟨j,hj⟩ := hd
      obtain ⟨k,hk⟩ := hb
      omega
  rcases hpd with hpd | hpd
  · exact prime_mod_eight_of_twice_square hp hp2 hpd hta
  · exact prime_mod_eight_of_twice_square hp hp2 hpd htb

#print axioms prime_mod_eight_of_quotient_four

end CrystalQuotientFour
