import LLS.NonresidueCert
import LLS.Numerics.IntervalsP
import LLS.Numerics.TailP
import LLS.Statement
import Ankeny.Character

/-!
# LLS Corollary 1.2 under GRH: the least quadratic non-residue mod a prime `q ≥ 5` is `≤ log² q`

* `5 ≤ q < 2^12`: kernel-checked certificates (`LLS.smallCert`, Euler's criterion).
* `q ≥ 2^12`: for prime `q > x` no prime power `≤ x` divides `q`, so the loss-free budget `Φ₁`
  applies (`LLS.Phi1_nonpos`); `GoodP 1 q` is certified by `IntervalsP` and `TailP`.
-/

set_option exponentiation.threshold 1024

namespace LLS

open Erdos985 (DirichletLNonvanishingRightOfHalf)

lemma checkFrom_get : ∀ (l : List (ℕ × ℕ)) (q₀ : ℕ), checkFrom q₀ l = true →
    ∀ i (h : i < l.length), certOK (q₀ + i) l[i].1 l[i].2 = true
  | [], _, _, i, h => by simp at h
  | e :: t, q₀, hc, i, h => by
    simp only [checkFrom, Bool.and_eq_true] at hc
    rcases i with _ | i
    · simpa using hc.1
    · have := checkFrom_get t (q₀ + 1) hc.2 i (by simpa using h)
      simpa [Nat.add_assoc, Nat.add_comm 1 i] using this

lemma cert_sound (q n k : ℕ) (hq : q.Prime) (hq5 : 5 ≤ q) (h : certOK q n k = true) :
    0 < n ∧ (n : ℝ) ≤ Real.log q ^ 2 ∧ ¬ IsSquare (n : ZMod q) := by
  simp only [certOK, Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq] at h
  obtain ⟨⟨⟨⟨hn0, hnq⟩, hk⟩, hnk⟩, hpow⟩ := h
  refine ⟨hn0, ?_, ?_⟩
  · have hl := log_ge_of_pow q k 16 (by norm_num) hk
    have hl0 : (0 : ℝ) ≤ (k : ℝ) / 16 * 0.6931471803 := by positivity
    have hnR : (n : ℝ) * 256 * 10 ^ 20 ≤ ((k : ℝ) * 6931471803) ^ 2 := by exact_mod_cast hnk
    have : (n : ℝ) ≤ ((k : ℝ) / 16 * 0.6931471803) ^ 2 := by nlinarith
    calc (n : ℝ) ≤ ((k : ℝ) / 16 * 0.6931471803) ^ 2 := this
      _ ≤ Real.log q ^ 2 := by gcongr; exact_mod_cast hl
  · rintro ⟨r, hr⟩
    have : Fact q.Prime := ⟨hq⟩
    have hn0' : (n : ZMod q) ≠ 0 := by
      rw [Ne, ZMod.natCast_eq_zero_iff]
      intro hd; exact absurd (Nat.le_of_dvd hn0 hd) (by omega)
    have hr0 : r ≠ 0 := by rintro rfl; simp at hr; exact hn0' hr
    have hodd : (q - 1) / 2 * 2 = q - 1 := by
      have := hq.eq_one_or_self_of_dvd 2
      have h2 : ¬ 2 ∣ q := fun hd => by have := this hd; omega
      omega
    have hF : r ^ (q - 1) = 1 := ZMod.pow_card_sub_one_eq_one hr0
    have h1 : ((n ^ ((q - 1) / 2) : ℕ) : ZMod q) = 1 := by
      push_cast
      rw [hr, ← pow_two, ← pow_mul, mul_comm, hodd, hF]
    have h2 : ((n ^ ((q - 1) / 2) % q : ℕ) : ZMod q) = 1 := by rw [ZMod.natCast_mod]; exact h1
    have h3 : n ^ ((q - 1) / 2) % q = 1 := by
      have := congrArg ZMod.val h2
      rw [ZMod.val_natCast, Nat.mod_mod, ZMod.val_one] at this
      exact this
    exact hpow h3

theorem nonresidue_small (q : ℕ) (hq : q.Prime) (hq5 : 5 ≤ q) (hq4096 : q < 4096) :
    ∃ n : ℕ, 0 < n ∧ (n : ℝ) ≤ Real.log q ^ 2 ∧ ¬ IsSquare (n : ZMod q) := by
  have hi : q - 5 < smallCert.length := by rw [smallCert_length]; omega
  have h := checkFrom_get smallCert 5 smallCert_ok (q - 5) hi
  rw [show 5 + (q - 5) = q by omega] at h
  exact ⟨_, cert_sound q _ _ hq hq5 h⟩

lemma log_sq_lt (q : ℕ) (hq : 4096 ≤ q) : Real.log q ^ 2 < q := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  set t := √(√(q : ℝ))
  have ht0 : 0 ≤ t := Real.sqrt_nonneg _
  have h1 : (√(q : ℝ)) ^ 2 = q := Real.sq_sqrt hq0.le
  have h2 : t ^ 2 = √(q : ℝ) := Real.sq_sqrt (Real.sqrt_nonneg _)
  have ht4 : t ^ 4 = q := by rw [← h1, ← h2]; ring
  have hqR : (4096 : ℝ) ≤ q := by exact_mod_cast hq
  have ht8 : 8 ≤ t := by
    by_contra h; push Not at h
    have : t ^ 4 < 8 ^ 4 := pow_lt_pow_left₀ h ht0 (by norm_num)
    norm_num at this; linarith
  have hlog : Real.log q = 4 * Real.log t := by
    rw [← ht4, Real.log_pow]; norm_num
  have hlt : Real.log t ≤ t - 1 := Real.log_le_sub_one_of_pos (by linarith)
  have hl0 : 0 ≤ Real.log t := Real.log_nonneg (by linarith)
  rw [hlog, ← ht4]
  have a1 : (4 * Real.log t) ^ 2 ≤ 16 * t ^ 2 := by nlinarith
  have a2 : 64 * t ^ 2 ≤ t ^ 2 * t ^ 2 := mul_le_mul_of_nonneg_right (by nlinarith) (sq_nonneg t)
  have a3 : 0 < t ^ 2 := by positivity
  have e : t ^ 4 = t ^ 2 * t ^ 2 := by ring
  rw [e]; linarith

theorem nonresidue_large (hGRH : DirichletLNonvanishingRightOfHalf) (q : ℕ) (hq : q.Prime)
    (hq4096 : 4096 ≤ q) :
    ∃ n : ℕ, 0 < n ∧ (n : ℝ) ≤ Real.log q ^ 2 ∧ ¬ IsSquare (n : ZMod q) := by
  have hgood : GoodP 1 q := by
    rcases lt_or_ge q (2 ^ 700) with h | h
    · exact IvP.goodP_range q (by simpa using hq4096) h
    · exact goodP_tail q h
  obtain ⟨x, hx64, hxc, hPhi⟩ := hgood
  rw [one_mul] at hxc
  have : Fact q.Prime := ⟨hq⟩
  have : NeZero q := ⟨hq.ne_zero⟩
  have : Fact (2 < q) := ⟨by omega⟩
  have hxq : x < q := by
    have := log_sq_lt q hq4096
    exact_mod_cast (lt_of_le_of_lt hxc this)
  by_contra hcon
  push Not at hcon
  let sq : (ZMod q)ˣ →* (ZMod q)ˣ := powMonoidHom 2
  have hH : sq.range ≠ ⊤ := by
    intro htop
    have hinj : Function.Injective sq :=
      Finite.injective_iff_surjective.2 (MonoidHom.range_eq_top.1 htop)
    have h1 : (-1 : (ZMod q)ˣ) = 1 := hinj (by simp [sq])
    exact ZMod.neg_one_ne_one (by simpa using congrArg Units.val h1)
  obtain ⟨χ, hχ, hχH⟩ := Ankeny.exists_dirichletCharacter_trivial_on sq.range hH
  have hval : ∀ n ≤ x, n.Coprime q → χ n = 1 := by
    intro n hn hcop
    set u := ZMod.unitOfCoprime n hcop
    have hn0 : 0 < n := by
      rcases Nat.eq_zero_or_pos n with rfl | h
      · simp at hcop; omega
      · exact h
    have hsq : IsSquare (n : ZMod q) := hcon n hn0 (le_trans (by exact_mod_cast hn) hxc)
    obtain ⟨r, hr⟩ := hsq
    have hr0 : r ≠ 0 := by
      rintro rfl
      have : (u : ZMod q) = 0 := by simpa [u] using hr
      exact u.ne_zero this
    have hu : u ∈ sq.range := ⟨Units.mk0 r hr0, Units.ext (by simp [sq, u, hr, pow_two])⟩
    simpa [u] using hχH u hu
  have := Phi1_nonpos hGRH hq χ hχ x hx64 hxq hval
  linarith

/-- **LLS Corollary 1.2 under GRH**: the least quadratic non-residue mod a prime `q ≥ 5` is at
most `(log q)²`. -/
theorem leastNonresidueBelowLogSq_of_GRH (hGRH : DirichletLNonvanishingRightOfHalf) :
    LeastNonresidueBelowLogSq := by
  intro q hq hq5
  rcases lt_or_ge q 4096 with h | h
  · exact nonresidue_small q hq hq5 h
  · exact nonresidue_large hGRH q hq h

end LLS
