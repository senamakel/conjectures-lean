import Mathlib

/-!
# A character of order `p` modulo `p²`

For an odd prime `p` we take a Dirichlet character `η` modulo `p²` with `η(a)^p = 1` on units and
`η(1 + p)` a primitive `p`-th root of unity. Its kernel contains every unit `a` with
`a ^ (p - 1) = 1`, and each power `η^j` with `0 < j < p` is primitive modulo `p²` (it does not
factor through level `p`, since it is non-trivial on `1 + p`, which is `1` modulo `p`).
-/

namespace PrimitiveRootSq

open DirichletCharacter

variable {p : ℕ} [hp : Fact p.Prime]

instance neZero_sq : NeZero (p ^ 2) := ⟨pow_ne_zero 2 hp.out.ne_zero⟩

omit hp in
lemma natCast_mul_self_eq_zero : (p : ZMod (p ^ 2)) * p = 0 := by
  rw [← Nat.cast_mul, ← sq, ZMod.natCast_self]

omit hp in
lemma one_add_pow_eq (n : ℕ) : (1 + p : ZMod (p ^ 2)) ^ n = 1 + n * p := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ (1 + (p : ZMod (p ^ 2))), ih]
    push_cast
    linear_combination (n : ZMod (p ^ 2)) * natCast_mul_self_eq_zero

lemma one_add_pow_self : (1 + p : ZMod (p ^ 2)) ^ p = 1 := by
  rw [one_add_pow_eq, natCast_mul_self_eq_zero, add_zero]

lemma one_add_ne_one : (1 + p : ZMod (p ^ 2)) ≠ 1 := by
  intro h
  have h0 : (p : ZMod (p ^ 2)) = 0 := by linear_combination h
  rw [ZMod.natCast_eq_zero_iff] at h0
  have h1 := Nat.le_of_dvd hp.out.pos h0
  have h2 := hp.out.two_le
  nlinarith

/-- A character modulo `p²` that is non-trivial on `1 + p` is primitive. -/
theorem isPrimitive_of_apply_one_add_ne_one {χ : DirichletCharacter ℂ (p ^ 2)}
    (h : χ (1 + (p : ZMod (p ^ 2))) ≠ 1) : χ.IsPrimitive := by
  rw [isPrimitive_def]
  obtain ⟨i, hi, hd⟩ := (Nat.dvd_prime_pow hp.out).1 (conductor_dvd_level χ)
  by_cases hi2 : i = 2
  · rw [hd, hi2]
  exfalso
  have hf : FactorsThrough χ (p ^ i) := hd ▸ factorsThrough_conductor χ
  have hfp : FactorsThrough χ p :=
    FactorsThrough.mono (χ := χ) (hχ := hf)
      (hd := by simpa using pow_dvd_pow p (show i ≤ 1 by omega)) (hm := dvd_pow_self p two_ne_zero)
  have hcop : IsCoprime ((1 + p : ℕ) : ℤ) ((p ^ 2 : ℕ) : ℤ) := by
    have : IsCoprime ((1 + p : ℕ) : ℤ) (p : ℤ) := ⟨1, -1, by push_cast; ring⟩
    simpa using this.pow_right (n := 2)
  apply h
  have e := changeLevel_eq_cast_of_dvd' hfp.χ₀ hfp.dvd hcop
  rw [← hfp.eq_changeLevel] at e
  have e1 : (((1 + p : ℕ) : ℤ) : ZMod (p ^ 2)) = 1 + p := by push_cast; ring
  have e2 : (((1 + p : ℕ) : ℤ) : ZMod p) = 1 := by push_cast; rw [ZMod.natCast_self, add_zero]
  rw [e1, e2, map_one] at e
  exact e

/-- The character `η`. -/
theorem exists_eta (hp2 : p ≠ 2) :
    ∃ η : DirichletCharacter ℂ (p ^ 2), (∀ a : ZMod (p ^ 2), IsUnit a → η a ^ p = 1) ∧
      ∀ j, 0 < j → j < p → η (1 + (p : ZMod (p ^ 2))) ^ j ≠ 1 := by
  have hp1 : p - 1 ≠ 0 := by have := hp.out.two_le; omega
  obtain ⟨χ, hχ⟩ := DirichletCharacter.exists_apply_ne_one_of_hasEnoughRootsOfUnity ℂ
    (one_add_ne_one (p := p))
  have hζp : χ (1 + (p : ZMod (p ^ 2))) ^ p = 1 := by rw [← map_pow, one_add_pow_self, map_one]
  have hζ : orderOf (χ (1 + (p : ZMod (p ^ 2)))) = p := orderOf_eq_prime hζp hχ
  refine ⟨χ ^ (p - 1), fun a ha => ?_, fun j hj0 hjp => ?_⟩
  · rw [MulChar.pow_apply' _ hp1, ← pow_mul, ← map_pow]
    have htot : (p ^ 2).totient = (p - 1) * p := by
      rw [Nat.totient_prime_pow hp.out (by norm_num)]; ring
    have : ha.unit ^ (p ^ 2).totient = 1 := ZMod.pow_totient ha.unit
    rw [htot] at this
    have : a ^ ((p - 1) * p) = 1 := by
      have := congrArg Units.val this
      simpa using this
    rw [this, map_one]
  · rw [MulChar.pow_apply' _ hp1, ← pow_mul]
    intro h1
    have hdvd : p ∣ (p - 1) * j := by
      have := orderOf_dvd_of_pow_eq_one h1; rwa [hζ] at this
    rcases (Nat.Prime.dvd_mul hp.out).1 hdvd with h | h
    · have := Nat.le_of_dvd (by omega) h; omega
    · have := Nat.le_of_dvd hj0 h; omega

end PrimitiveRootSq
