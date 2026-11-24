import Mathlib
import GoldbachCheck

/-!
# Soundness of the prime ladder

`prime_of_pockOK`: Pocklington's criterion with a prime-power part. If `F = p^e` (`p` prime,
`e ≥ 1`) divides `c − 1`, `F² > c`, `a^(c−1) ≡ 1 (mod c)` and `gcd(a^((c−1)/p) − 1, c) = 1`,
then `c` is prime: for a prime `q ∣ c`, `y = a^((c−1)/F)` has order exactly `p^e` in
`(ZMod q)ˣ`, so `p^e ∣ q − 1` and `q > F > √c`.

`ladderCover_sound`: if `ladderCover G lo hi = true`, every `y ∈ [lo, hi]` has a prime
`q ≤ y` with `y < q + G`.
-/

namespace Goldbach.Check

theorem powModAux_eq (m b e acc : ℕ) : powModAux m b e acc = acc * b ^ e % m := by
  induction e using Nat.strong_induction_on generalizing b acc with
  | _ e ih =>
    rw [powModAux]
    split_ifs with h0 h1
    · simp [h0]
    · rw [ih (e / 2) (by omega), ← ZMod.natCast_eq_natCast_iff']
      push_cast [ZMod.natCast_mod]
      conv_rhs => rw [← Nat.div_add_mod e 2, h1]
      ring
    · rw [ih (e / 2) (by omega), ← ZMod.natCast_eq_natCast_iff']
      push_cast [ZMod.natCast_mod]
      have h2 : e % 2 = 0 := by omega
      conv_rhs => rw [← Nat.div_add_mod e 2, h2]
      ring

theorem powMod_eq (b e m : ℕ) : powMod b e m = b ^ e % m := by
  rw [powMod, powModAux_eq, one_mul, ← Nat.pow_mod]

/-- Pocklington: every prime factor `q` of a `c` passing `pockOK` has `p^e ∣ q − 1`. -/
theorem pow_dvd_sub_one_of_pockOK {c p e a q : ℕ} (hp : p.Prime) (h : pockOK c p e a = true)
    (hq : q.Prime) (hqc : q ∣ c) : p ^ e ∣ q - 1 := by
  unfold pockOK at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨he, hc2⟩, -⟩, hF⟩, hfer⟩, hgcd⟩ := h
  have := Fact.mk hq
  have := Fact.mk hp
  rw [powMod_eq] at hfer hgcd
  set F := p ^ e
  obtain ⟨R, hR⟩ : F ∣ c - 1 := Nat.dvd_of_mod_eq_zero hF
  -- `a^(c−1) = 1` in `ZMod q`
  have hcast : ∀ x : ℕ, ((x % c : ℕ) : ZMod q) = (x : ZMod q) := by
    intro x
    rw [ZMod.natCast_eq_natCast_iff]
    exact (Nat.mod_modEq x c).of_dvd hqc
  have hone : (a : ZMod q) ^ (c - 1) = 1 := by
    have := hcast (a ^ (c - 1)); rw [hfer] at this; push_cast at this; exact this.symm
  set y := (a : ZMod q) ^ R
  have hy1 : y ^ p ^ e = 1 := by
    rw [← pow_mul, mul_comm, ← hR]; exact hone
  obtain ⟨n, rfl⟩ : ∃ n, e = n + 1 := ⟨e - 1, by omega⟩
  have hdiv : (c - 1) / p = R * p ^ n := by
    rw [hR]; show p ^ (n + 1) * R / p = R * p ^ n
    rw [pow_succ, mul_comm (p ^ n) p, mul_assoc, Nat.mul_div_cancel_left _ hp.pos, mul_comm]
  have hy2 : ¬ y ^ p ^ n = 1 := by
    intro hy
    rw [← pow_mul, ← hdiv] at hy
    -- then `q` divides `(x + c − 1) % c` and `c`, contradicting the gcd
    have hdvd : q ∣ ((a ^ ((c - 1) / p) % c + c - 1) % c).gcd c := by
      refine Nat.dvd_gcd ?_ hqc
      rw [← ZMod.natCast_eq_zero_iff, hcast]
      have hc0 : (c : ZMod q) = 0 := (ZMod.natCast_eq_zero_iff c q).mpr hqc
      have e1 : a ^ ((c - 1) / p) % c + c - 1 = a ^ ((c - 1) / p) % c + (c - 1) := by omega
      rw [e1]
      push_cast [hcast, Nat.cast_sub (show 1 ≤ c by omega), hc0, hy]
      ring
    rw [hgcd] at hdvd
    exact hq.one_lt.ne' (Nat.dvd_one.mp hdvd)
  have hord : orderOf y = p ^ (n + 1) := orderOf_eq_prime_pow hy2 hy1
  have hy0 : y ≠ 0 := by
    intro h0; rw [h0, zero_pow (pow_ne_zero _ hp.ne_zero)] at hy1; exact zero_ne_one hy1
  show p ^ (n + 1) ∣ q - 1
  rw [← hord]
  exact ZMod.orderOf_dvd_card_sub_one hy0

theorem prime_of_pockOK {c p e a : ℕ} (hp : p.Prime) (h : pockOK c p e a = true) : c.Prime := by
  have h' := h
  unfold pockOK at h'
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h'
  obtain ⟨⟨⟨⟨⟨he, hc2⟩, hcF⟩, -⟩, -⟩, -⟩ := h'
  by_contra hnp
  set q := c.minFac
  have hq : q.Prime := Nat.minFac_prime (by omega)
  have hd := pow_dvd_sub_one_of_pockOK hp h hq (Nat.minFac_dvd c)
  have hqF : p ^ e < q := by
    have h1 : p ^ e ≤ q - 1 := Nat.le_of_dvd (Nat.sub_pos_of_lt hq.one_lt) hd
    have h2 := hq.two_le
    omega
  have hsq : q ^ 2 ≤ c := Nat.minFac_sq_le_self (by omega) hnp
  have : p ^ e * p ^ e < q * q := Nat.mul_self_lt_mul_self hqF
  rw [sq] at hsq
  have := lt_of_lt_of_le this hsq
  omega

theorem prime_of_mem_ladderBases {p : ℕ} (h : ladderBases.contains p = true) : p.Prime := by
  simp only [ladderBases, List.contains_eq_mem, List.mem_cons, List.mem_nil_iff, or_false,
    decide_eq_true_eq] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num

/-- Every `y ∈ [c, hi]` has a prime `q ≤ y` with `y < q + G`. -/
def Covers (G c hi : ℕ) : Prop := ∀ y, c ≤ y → y ≤ hi → ∃ q, q.Prime ∧ q ≤ y ∧ y < q + G

theorem ladderTo_sound {G hi : ℕ} (hG : 0 < G) :
    ∀ f c, c.Prime → ladderTo G hi c f = true → Covers G c hi
  | 0, c, hc, h, y, h1, h2 => by
    simp only [ladderTo, decide_eq_true_eq] at h
    exact ⟨c, hc, h1, by omega⟩
  | f + 1, c, hc, h, y, h1, h2 => by
    unfold ladderTo at h
    split_ifs at h with hhi
    · exact ⟨c, hc, h1, by omega⟩
    · split at h
      · next c' p e a _ =>
        simp only [rungOK, Bool.and_eq_true, decide_eq_true_eq] at h
        obtain ⟨⟨⟨⟨hpock, hbase⟩, hlt⟩, hle⟩, hrest⟩ := h
        have hc' : c'.Prime := prime_of_pockOK (prime_of_mem_ladderBases hbase) hpock
        by_cases hy : y < c'
        · exact ⟨c, hc, h1, by omega⟩
        · exact ladderTo_sound hG f c' hc' hrest y (by omega) h2
      · exact absurd h (by simp)

theorem ladderCover_sound {G lo hi : ℕ} (hG : 0 < G) (h : ladderCover G lo hi = true) :
    Covers G lo hi := by
  unfold ladderCover at h
  split at h
  · next c p e a _ =>
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨⟨hpock, hbase⟩, hle⟩, hrest⟩ := h
    have hc : c.Prime := prime_of_pockOK (prime_of_mem_ladderBases hbase) hpock
    intro y h1 h2
    exact ladderTo_sound hG _ c hc hrest y (by omega) h2
  · exact absurd h (by simp)

end Goldbach.Check
