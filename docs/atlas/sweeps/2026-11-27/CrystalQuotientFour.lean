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

end CrystalQuotientFour
