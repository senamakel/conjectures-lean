import BachCorollaries.Statement

/-!
# The Euler liars form a proper subgroup

For odd `n`, the units `u` of `ZMod n` with `u^((n-1)/2) = (u/n)` (Jacobi symbol) form a
subgroup `eulerLiars n` of `(ZMod n)ˣ`, since the Jacobi symbol is multiplicative in its first
argument. Solovay and Strassen (1977) observed that it is proper when `n` is composite:

* if `p² ∣ n`, the unit `v = 1 + n/p` has `v^(n-1) = 1 - n/p ≠ 1`, while every Euler liar `u`
  has `u^(n-1) = (u/n)² = 1`;
* if `n = p m` with `p ∤ m` and `m > 1`, take `k ≡ x (mod p)`, `k ≡ 1 (mod m)` for a quadratic
  non-residue `x` mod `p`. Then `(k/n) = (k/p)(k/m) = -1`, but `k^((n-1)/2) ≡ 1 (mod m)`, so
  `k^((n-1)/2) ≢ -1 (mod n)`.
-/

namespace BachCorollaries

/-- The Jacobi symbol `(u/n)` of a unit mod `n`, through its least residue. -/
def unitJacobi (n : ℕ) (u : (ZMod n)ˣ) : ℤ := jacobiSym ((u : ZMod n).val : ℤ) n

theorem jacobi_val_mul {n : ℕ} [NeZero n] (x y : ZMod n) :
    jacobiSym (((x * y).val : ℕ) : ℤ) n =
      jacobiSym ((x.val : ℕ) : ℤ) n * jacobiSym ((y.val : ℕ) : ℤ) n := by
  rw [ZMod.val_mul, Int.natCast_mod, ← jacobiSym.mod_left, Nat.cast_mul, jacobiSym.mul_left]

theorem unitJacobi_mul {n : ℕ} [NeZero n] (u v : (ZMod n)ˣ) :
    unitJacobi n (u * v) = unitJacobi n u * unitJacobi n v := by
  unfold unitJacobi
  rw [Units.val_mul, jacobi_val_mul]

theorem unitJacobi_one (n : ℕ) [NeZero n] : unitJacobi n 1 = 1 := by
  unfold unitJacobi
  rw [Units.val_one, ZMod.val_one_eq_one_mod, Int.natCast_mod, ← jacobiSym.mod_left,
    Nat.cast_one, jacobiSym.one_left]

theorem unitJacobi_eq_one_or_neg_one {n : ℕ} [NeZero n] (u : (ZMod n)ˣ) :
    unitJacobi n u = 1 ∨ unitJacobi n u = -1 := by
  apply jacobiSym.eq_one_or_neg_one
  rw [Int.gcd_natCast_natCast]
  exact ZMod.val_coe_unit_coprime u

theorem unitJacobi_cast_sq {n : ℕ} [NeZero n] (u : (ZMod n)ˣ) :
    ((unitJacobi n u : ℤ) : ZMod n) * ((unitJacobi n u : ℤ) : ZMod n) = 1 := by
  rcases unitJacobi_eq_one_or_neg_one u with h | h <;> simp [h]

/-- The Euler liars mod `n`: units `u` with `u^((n-1)/2) = (u/n)`. -/
def eulerLiars (n : ℕ) [NeZero n] : Subgroup (ZMod n)ˣ where
  carrier := {u | (u : ZMod n) ^ ((n - 1) / 2) = ((unitJacobi n u : ℤ) : ZMod n)}
  mul_mem' := by
    intro u v hu hv
    simp only [Set.mem_ofPred_eq] at *
    rw [Units.val_mul, mul_pow, hu, hv, unitJacobi_mul, Int.cast_mul]
  one_mem' := by
    simp only [Set.mem_ofPred_eq, Units.val_one, one_pow, unitJacobi_one, Int.cast_one]
  inv_mem' := by
    intro u hu
    simp only [Set.mem_ofPred_eq] at *
    have hJ : unitJacobi n u⁻¹ = unitJacobi n u := by
      have h1 := unitJacobi_mul u⁻¹ u
      rw [inv_mul_cancel, unitJacobi_one] at h1
      rcases unitJacobi_eq_one_or_neg_one u with h | h <;> rw [h] at h1 ⊢ <;> linarith
    have hm : ((u⁻¹ : (ZMod n)ˣ) : ZMod n) ^ ((n - 1) / 2) * (u : ZMod n) ^ ((n - 1) / 2) = 1 := by
      rw [← mul_pow, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_pow]
    rw [hJ]
    calc ((u⁻¹ : (ZMod n)ˣ) : ZMod n) ^ ((n - 1) / 2)
        = ((u⁻¹ : (ZMod n)ˣ) : ZMod n) ^ ((n - 1) / 2) *
            (((unitJacobi n u : ℤ) : ZMod n) * ((unitJacobi n u : ℤ) : ZMod n)) := by
          rw [unitJacobi_cast_sq, mul_one]
      _ = (((u⁻¹ : (ZMod n)ˣ) : ZMod n) ^ ((n - 1) / 2) * (u : ZMod n) ^ ((n - 1) / 2)) *
            ((unitJacobi n u : ℤ) : ZMod n) := by rw [hu]; ring
      _ = ((unitJacobi n u : ℤ) : ZMod n) := by rw [hm, one_mul]

theorem mem_eulerLiars_iff {n : ℕ} [NeZero n] (u : (ZMod n)ˣ) :
    u ∈ eulerLiars n ↔ IsEulerProbablePrime n (u : ZMod n).val := by
  change _ = _ ↔ _
  rw [IsEulerProbablePrime, ZMod.natCast_zmod_val]
  rfl

/-- Case `p² ∣ n`: the unit `1 + n/p` is not an Euler liar. -/
theorem eulerLiars_ne_top_of_sq_dvd {n p : ℕ} [NeZero n] (hn : Odd n) (hp : p.Prime)
    (hpn : p ^ 2 ∣ n) : eulerLiars n ≠ ⊤ := by
  have hp1 : p ∣ n := (dvd_pow_self p two_ne_zero).trans hpn
  have hn0 : n ≠ 0 := NeZero.ne n
  set m := n / p with hmdef
  have hnm : p * m = n := Nat.mul_div_cancel' hp1
  have hpm : p ∣ m := Nat.dvd_div_of_mul_dvd (by rw [← sq]; exact hpn)
  obtain ⟨k, hk⟩ := hpm
  have hmm : (m : ZMod n) * m = 0 := by
    rw [← Nat.cast_mul, ZMod.natCast_eq_zero_iff]
    exact ⟨k, by rw [← hnm]; nth_rw 2 [hk]; ring⟩
  have hpm0 : (p : ZMod n) * m = 0 := by
    rw [← Nat.cast_mul, hnm, ZMod.natCast_self]
  set v : ZMod n := 1 + m with hv
  have hpow : ∀ j : ℕ, v ^ j = 1 + (j : ZMod n) * m := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      rw [pow_succ, ih, hv]
      push_cast
      linear_combination (j : ZMod n) * hmm
  have hvp : v ^ p = 1 := by rw [hpow, hpm0, add_zero]
  have he : n - 1 = 2 * ((n - 1) / 2) := by obtain ⟨j, hj⟩ := hn; omega
  have hn1 : ((n - 1 : ℕ) : ZMod n) = -1 := by
    rw [Nat.cast_sub (by omega), ZMod.natCast_self, Nat.cast_one, zero_sub]
  intro htop
  set U := Units.ofPowEqOne v p hvp hp.ne_zero
  have hU : U ∈ eulerLiars n := htop ▸ Subgroup.mem_top U
  change (U : ZMod n) ^ ((n - 1) / 2) = _ at hU
  have hU' : v ^ ((n - 1) / 2) = ((unitJacobi n U : ℤ) : ZMod n) := by
    rwa [Units.val_ofPowEqOne] at hU
  have hsq : v ^ (n - 1) = 1 := by
    rw [he, pow_mul', sq, hU', unitJacobi_cast_sq]
  rw [hpow, hn1, neg_one_mul, add_eq_left, neg_eq_zero, ZMod.natCast_eq_zero_iff] at hsq
  have hm0 : 0 < m := Nat.div_pos (Nat.le_of_dvd (by omega) hp1) hp.pos
  have hmn : m < n := Nat.div_lt_self (by omega) hp.one_lt
  exact absurd (Nat.le_of_dvd hm0 hsq) (by omega)

/-- Case `n = p m` with `p` prime, `p ∤ m`, `m > 2`: a CRT lift of a non-residue mod `p` that is
`1` mod `m` is not an Euler liar. -/
theorem eulerLiars_ne_top_of_coprime {p m : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hcop : p.Coprime m)
    (hm : 2 < m) [NeZero (p * m)] : eulerLiars (p * m) ≠ ⊤ := by
  have : Fact p.Prime := ⟨hp⟩
  have : NeZero p := ⟨hp.ne_zero⟩
  have : NeZero m := ⟨by omega⟩
  have : Fact (2 < m) := ⟨hm⟩
  obtain ⟨x, hx⟩ := FiniteField.exists_nonsquare (F := ZMod p) (by rwa [ZMod.ringChar_zmod_n])
  obtain ⟨k, hkp, hkm⟩ := Nat.chineseRemainder hcop x.val 1
  have hkp' : (k : ZMod p) = x := by
    rw [(ZMod.natCast_eq_natCast_iff k x.val p).mpr hkp, ZMod.natCast_zmod_val]
  have hkm' : (k : ZMod m) = 1 := by
    rw [(ZMod.natCast_eq_natCast_iff k 1 m).mpr hkm, Nat.cast_one]
  have hx0 : x ≠ 0 := by rintro rfl; exact hx ⟨0, by simp⟩
  have hcp : k.Coprime p := (Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd hp).mpr
    fun h => hx0 (by rw [← hkp', (ZMod.natCast_eq_zero_iff k p).mpr h])))
  have hcm : k.Coprime m := by
    rw [Nat.Coprime, Nat.ModEq.gcd_eq hkm, Nat.gcd_one_left]
  have hcn : k.Coprime (p * m) := Nat.Coprime.mul_right hcp hcm
  have hJp : jacobiSym (k : ℤ) p = -1 := by
    rw [← jacobiSym.legendreSym.to_jacobiSym, legendreSym.eq_neg_one_iff, Int.cast_natCast, hkp']
    exact hx
  have hJm : jacobiSym (k : ℤ) m = 1 := by
    rw [jacobiSym.mod_left, ← Int.natCast_mod, show k % m = 1 by
      have h : k % m = 1 % m := hkm
      rw [h, Nat.mod_eq_of_lt (by omega)], Nat.cast_one, jacobiSym.one_left]
  have hJ : unitJacobi (p * m) (ZMod.unitOfCoprime k hcn) = -1 := by
    unfold unitJacobi
    rw [ZMod.coe_unitOfCoprime, ZMod.val_natCast, Int.natCast_mod, ← jacobiSym.mod_left,
      jacobiSym.mul_right, hJp, hJm]
    norm_num
  intro htop
  have hU : ZMod.unitOfCoprime k hcn ∈ eulerLiars (p * m) := htop ▸ Subgroup.mem_top _
  change _ = _ at hU
  rw [hJ, ZMod.coe_unitOfCoprime] at hU
  have := congrArg (ZMod.castHom (Dvd.intro_left p rfl : m ∣ p * m) (ZMod m)) hU
  rw [map_pow, map_natCast, hkm', one_pow, map_intCast, Int.cast_neg, Int.cast_one] at this
  exact ZMod.neg_one_ne_one this.symm

/-- **Solovay–Strassen.** For odd composite `n`, the Euler liars form a proper subgroup. -/
theorem eulerLiars_ne_top {n : ℕ} [NeZero n] (hn : Odd n) (h1 : 1 < n) (hnp : ¬ n.Prime) :
    eulerLiars n ≠ ⊤ := by
  set p := n.minFac with hpdef
  have hp : p.Prime := Nat.minFac_prime (by omega)
  have hpn : p ∣ n := Nat.minFac_dvd n
  have hk1 : 1 ≤ n.factorization p := (hp.dvd_iff_one_le_factorization (by omega)).mp hpn
  by_cases hk : 2 ≤ n.factorization p
  · exact eulerLiars_ne_top_of_sq_dvd hn hp ((pow_dvd_pow p hk).trans (Nat.ordProj_dvd n p))
  · have hk' : n.factorization p = 1 := by omega
    obtain ⟨m, hnm, hcop⟩ : ∃ m, n = p * m ∧ p.Coprime m := by
      refine ⟨n / p ^ n.factorization p, ?_, Nat.coprime_ordCompl hp (by omega)⟩
      conv_lhs => rw [← Nat.ordProj_mul_ordCompl_eq_self n p]
      rw [hk', pow_one]
    have hp2 : p ≠ 2 := by
      intro h2
      have := Nat.odd_iff.mp (Odd.of_dvd_nat hn hpn)
      omega
    have hm2 : 2 < m := by
      have hmo : Odd m := Odd.of_dvd_nat hn ⟨p, by rw [hnm, mul_comm]⟩
      have hm1 : m ≠ 1 := by rintro rfl; rw [mul_one] at hnm; exact hnp (hnm ▸ hp)
      have hm0 : m ≠ 0 := by rintro rfl; omega
      obtain ⟨j, rfl⟩ := hmo
      omega
    have key : ∀ N, N = p * m → ∀ [NeZero N], eulerLiars N ≠ ⊤ := by
      rintro N rfl _
      exact eulerLiars_ne_top_of_coprime hp hp2 hcop hm2
    exact key n hnm

end BachCorollaries
