import Miller.Basic

/-!
# The strong liars lie in a proper subgroup

For odd composite `n`, the units of `ZMod n` that are strong liars lie in a proper subgroup of
`(ZMod n)ˣ` (Conrad, "The Miller–Rabin test"; Crandall–Pomerance §3.5).

* If `p² ∣ n`, the Fermat liars `{u : u^(n-1) = 1}` form a proper subgroup: the unit `1 + n/p`
  has order `p`, and `p ∤ n - 1`.
* If `n = a b` with `a, b > 2` coprime, let `r₀` be the largest `r < s` for which some unit has
  `w^(2^r d) = -1`. The subgroup `{u : u^(2^{r₀} d) = ±1}` contains every strong liar, and the
  unit corresponding to `(w, 1)` under the Chinese remainder theorem is not in it.
-/

namespace Miller

/-- Case `p² ∣ n`: the Fermat liars form a proper subgroup containing all strong liars. -/
theorem exists_subgroup_of_sq_dvd {n p : ℕ} (hp : p.Prime) (hpn : p ^ 2 ∣ n) (h1 : 1 < n) :
    ∃ H : Subgroup (ZMod n)ˣ, H ≠ ⊤ ∧ ∀ u, IsLiar n u → u ∈ H := by
  refine ⟨(powMonoidHom (n - 1) : (ZMod n)ˣ →* (ZMod n)ˣ).ker, ?_, ?_⟩
  · obtain ⟨k, hk⟩ := hpn
    have hk0 : 0 < k := Nat.pos_of_ne_zero (by rintro rfl; simp at hk; omega)
    set m : ZMod n := ((p * k : ℕ) : ZMod n) with hm
    have hmm : m * m = 0 := by
      rw [hm, ← Nat.cast_mul, ZMod.natCast_eq_zero_iff]
      exact ⟨k, by rw [hk]; ring⟩
    have hpm : (p : ZMod n) * m = 0 := by
      rw [hm, ← Nat.cast_mul, ZMod.natCast_eq_zero_iff]
      exact ⟨1, by rw [hk]; ring⟩
    have hpow : ∀ j : ℕ, (1 + m) ^ j = 1 + (j : ZMod n) * m := by
      intro j
      induction j with
      | zero => simp
      | succ j ih =>
        rw [pow_succ, ih]
        push_cast
        linear_combination (j : ZMod n) * hmm
    have hp1 : (1 + m) ^ p = 1 := by rw [hpow, hpm, add_zero]
    intro htop
    have hu : Units.ofPowEqOne (1 + m) p hp1 hp.ne_zero ∈
        (powMonoidHom (n - 1) : (ZMod n)ˣ →* (ZMod n)ˣ).ker := htop ▸ Subgroup.mem_top _
    rw [MonoidHom.mem_ker, powMonoidHom_apply] at hu
    have hup : (Units.ofPowEqOne (1 + m) p hp1 hp.ne_zero) ^ p = 1 :=
      Units.pow_ofPowEqOne _ _
    have hcop : Nat.gcd (n - 1) p = 1 := by
      refine Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hp).2 fun h => ?_)
      have hpn' : p ∣ n := Dvd.dvd.trans (dvd_pow_self p two_ne_zero) ⟨k, hk⟩
      have : p ∣ n - (n - 1) := Nat.dvd_sub hpn' h
      rw [show n - (n - 1) = 1 by omega] at this
      exact hp.one_lt.ne' (Nat.dvd_one.mp this)
    have h1u := pow_gcd_eq_one.mpr ⟨hu, hup⟩
    rw [hcop, pow_one, Units.ext_iff, Units.val_ofPowEqOne, Units.val_one,
      add_eq_left, hm, ZMod.natCast_eq_zero_iff] at h1u
    have := Nat.le_of_dvd (Nat.mul_pos hp.pos hk0) h1u
    have hp2 := hp.two_le
    rw [hk] at this
    nlinarith
  · intro u hu
    rw [MonoidHom.mem_ker, powMonoidHom_apply, ← two_pow_sPart_mul_dPart]
    rcases hu with h | ⟨r, hr, h⟩
    · rw [mul_comm, pow_mul, h, one_pow]
    · have : 2 ^ sPart n * dPart n = 2 ^ r * dPart n * 2 ^ (sPart n - r) := by
        rw [mul_right_comm, ← pow_add, Nat.add_sub_cancel' hr.le]
      rw [this, pow_mul, h, (Nat.even_pow.mpr ⟨even_two, by omega⟩).neg_one_pow]

/-- Case `n = a b` with `a, b > 2` coprime. Only `d` odd and `s > 0` are used. -/
theorem exists_subgroup_of_coprime {a b : ℕ} (hab : a.Coprime b) (ha : 2 < a) (hb : 2 < b)
    {s d : ℕ} (hd : Odd d) (hs : 0 < s) :
    ∃ H : Subgroup (ZMod (a * b))ˣ, H ≠ ⊤ ∧
      ∀ u, (u ^ d = 1 ∨ ∃ r < s, u ^ (2 ^ r * d) = -1) → u ∈ H := by
  classical
  let P : ℕ → Prop := fun r => ∃ w : (ZMod (a * b))ˣ, w ^ (2 ^ r * d) = -1
  have P0 : P 0 := ⟨-1, by simp [hd.neg_one_pow]⟩
  set r₀ := Nat.findGreatest P (s - 1) with hr₀def
  obtain ⟨w, hw⟩ : P r₀ := Nat.findGreatest_spec (Nat.zero_le _) P0
  have hr₀s : r₀ < s := by have := Nat.findGreatest_le (P := P) (s - 1); omega
  let H : Subgroup (ZMod (a * b))ˣ :=
    { carrier := {u | u ^ (2 ^ r₀ * d) = 1 ∨ u ^ (2 ^ r₀ * d) = -1}
      mul_mem' := by
        rintro x y (hx | hx) (hy | hy) <;> simp [mul_pow, hx, hy]
      one_mem' := by simp
      inv_mem' := by
        rintro x (hx | hx) <;> simp [inv_pow, hx] }
  refine ⟨H, ?_, ?_⟩
  · -- the CRT construction
    have : Fact (2 < a) := ⟨ha⟩
    have : Fact (2 < b) := ⟨hb⟩
    let cr := ZMod.chineseRemainder hab
    obtain ⟨x, hxdef⟩ : ∃ x, x = (cr (w : ZMod (a * b))).1 := ⟨_, rfl⟩
    have hx : IsUnit x := hxdef ▸ (Prod.isUnit_iff.mp (w.isUnit.map cr)).1
    have hv : IsUnit (cr.symm (x, 1)) := by
      apply IsUnit.map
      exact Prod.isUnit_iff.mpr ⟨hx, isUnit_one⟩
    have hxe : x ^ (2 ^ r₀ * d) = -1 := by
      have := congrArg (fun z : (ZMod (a * b))ˣ => (cr (z : ZMod (a * b))).1) hw
      simpa [hxdef] using this
    have key : cr ((hv.unit : ZMod (a * b)) ^ (2 ^ r₀ * d)) = (-1, 1) := by
      rw [IsUnit.unit_spec, map_pow, RingEquiv.apply_symm_apply, Prod.pow_mk, hxe, one_pow]
    intro htop
    have hmem : hv.unit ∈ H := htop ▸ Subgroup.mem_top _
    rcases hmem with h | h
    · rw [Units.ext_iff, Units.val_pow_eq_pow_val, Units.val_one] at h
      rw [h, map_one] at key
      exact ZMod.neg_one_ne_one (congrArg Prod.fst key).symm
    · rw [Units.ext_iff, Units.val_pow_eq_pow_val, Units.val_neg, Units.val_one] at h
      rw [h, map_neg, map_one] at key
      exact ZMod.neg_one_ne_one (congrArg Prod.snd key)
  · rintro u (h | ⟨r, hr, h⟩)
    · left
      rw [show 2 ^ r₀ * d = d * 2 ^ r₀ from mul_comm _ _, pow_mul, h, one_pow]
    · have hle : r ≤ r₀ := Nat.le_findGreatest (by omega) ⟨u, h⟩
      rcases hle.eq_or_lt with rfl | hlt
      · exact Or.inr h
      · left
        have : 2 ^ r₀ * d = 2 ^ r * d * 2 ^ (r₀ - r) := by
          rw [mul_right_comm, ← pow_add, Nat.add_sub_cancel' hlt.le]
        rw [this, pow_mul, h, (Nat.even_pow.mpr ⟨even_two, by omega⟩).neg_one_pow]

/-- **Key lemma.** For odd composite `n`, the strong liars among the units lie in a proper
subgroup of `(ZMod n)ˣ`. -/
theorem exists_proper_subgroup_liars {n : ℕ} (hn : Odd n) (h1 : 1 < n) (hnp : ¬ n.Prime) :
    ∃ H : Subgroup (ZMod n)ˣ, H ≠ ⊤ ∧ ∀ u, IsLiar n u → u ∈ H := by
  set p := n.minFac with hpdef
  have hp : p.Prime := Nat.minFac_prime (by omega)
  have hpn : p ∣ n := Nat.minFac_dvd n
  have hk1 : 1 ≤ n.factorization p := (hp.dvd_iff_one_le_factorization (by omega)).mp hpn
  by_cases hk : 2 ≤ n.factorization p
  · exact exists_subgroup_of_sq_dvd hp
      ((pow_dvd_pow p hk).trans (Nat.ordProj_dvd n p)) h1
  · have hk' : n.factorization p = 1 := by omega
    obtain ⟨m, hnm, hcop⟩ : ∃ m, n = p * m ∧ p.Coprime m := by
      refine ⟨n / p ^ n.factorization p, ?_, Nat.coprime_ordCompl hp (by omega)⟩
      conv_lhs => rw [← Nat.ordProj_mul_ordCompl_eq_self n p]
      rw [hk', pow_one]
    have hp2 : 2 < p := by
      have := Nat.odd_iff.mp (Odd.of_dvd_nat hn hpn)
      have := hp.two_le
      omega
    have hm2 : 2 < m := by
      have hmo : Odd m := Odd.of_dvd_nat hn ⟨p, by rw [hnm, mul_comm]⟩
      have hm1 : m ≠ 1 := by rintro rfl; rw [mul_one] at hnm; exact hnp (hnm ▸ hp)
      have hm0 : m ≠ 0 := by rintro rfl; omega
      obtain ⟨j, rfl⟩ := hmo
      omega
    have := exists_subgroup_of_coprime hcop hp2 hm2 (odd_dPart h1) (sPart_pos hn h1)
    rw [← hnm] at this
    exact this

end Miller
