import Mathlib

namespace BachSharp

/-! Torsion counts for unit groups of `ZMod`, for the bach-sharp-gap Frattini certificate
(PR #29, STATUS.md step 2). -/

theorem torsion_card_cyclic_le {G : Type*} [CommGroup G] [Finite G] [IsCyclic G] (n : ℕ)
    (hn : 0 < n) : Nat.card {u : G // u ^ n = 1} ≤ n := by
  classical
  have := Fintype.ofFinite G
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  exact IsCyclic.card_pow_eq_one_le hn

/-- Odd prime powers: the unit group is cyclic, so it has at most `ℓ` elements of order dividing `ℓ`. -/
theorem card_torsion_units_odd_prime_pow_le (p e ℓ : ℕ) [Fact p.Prime] (hp : p ≠ 2) (hℓ : ℓ.Prime) :
    Nat.card {u : (ZMod (p ^ e))ˣ // u ^ ℓ = 1} ≤ ℓ := by
  have : NeZero (p ^ e) := ⟨pow_ne_zero _ (Fact.out : p.Prime).ne_zero⟩
  have : IsCyclic (ZMod (p ^ e))ˣ := ZMod.isCyclic_units_of_prime_pow p Fact.out hp e
  exact torsion_card_cyclic_le ℓ hℓ.pos

/-- Odd `ℓ`: no nontrivial `ℓ`-torsion modulo a power of two. -/
theorem card_torsion_units_two_pow_odd (e ℓ : ℕ) (hℓ : ℓ.Prime) (hodd : ℓ ≠ 2) :
    Nat.card {u : (ZMod (2 ^ e))ˣ // u ^ ℓ = 1} = 1 := by
  have : NeZero (2 ^ e) := ⟨pow_ne_zero _ two_ne_zero⟩
  have hsub : Subsingleton {u : (ZMod (2 ^ e))ˣ // u ^ ℓ = 1} := by
    refine ⟨fun a b => ?_⟩
    have h1 : ∀ u : (ZMod (2 ^ e))ˣ, u ^ ℓ = 1 → u = 1 := by
      intro u hu
      have h2 : orderOf u ∣ ℓ := orderOf_dvd_of_pow_eq_one hu
      have h3 : orderOf u ∣ 2 ^ e := by
        refine (orderOf_dvd_natCard u).trans ?_
        rw [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient]
        rcases e with _ | e
        · simp
        · rw [Nat.totient_prime_pow_succ Nat.prime_two]; simp [pow_succ]
      have hc : Nat.Coprime ℓ (2 ^ e) :=
        Nat.Coprime.pow_right _ ((Nat.coprime_primes hℓ Nat.prime_two).2 hodd)
      have : orderOf u ∣ 1 := by
        have := Nat.dvd_gcd h2 h3
        rwa [hc] at this
      exact orderOf_eq_one_iff.1 (Nat.dvd_one.1 this)
    exact Subtype.ext ((h1 _ a.2).trans (h1 _ b.2).symm)
  have : Nonempty {u : (ZMod (2 ^ e))ˣ // u ^ ℓ = 1} := ⟨⟨1, one_pow _⟩⟩
  exact Nat.card_eq_one_iff_unique.2 ⟨hsub, ‹_›⟩

theorem torsion_card_sq_le_four {G : Type*} [CommGroup G] [Finite G] (N : Subgroup G)
    (hN : Nat.card N ≤ 2) [IsCyclic (G ⧸ N)] : Nat.card {u : G // u ^ 2 = 1} ≤ 4 := by
  classical
  have := Fintype.ofFinite G
  have := Fintype.ofFinite N
  have := Fintype.ofFinite (G ⧸ N)
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  set s : Finset G := Finset.univ.filter (fun u : G => u ^ 2 = 1) with hs
  have hcard : (s.image (QuotientGroup.mk : G → G ⧸ N)).card ≤ 2 := by
    refine le_trans (Finset.card_le_card ?_) (by
      have := IsCyclic.card_pow_eq_one_le (α := G ⧸ N) (n := 2) (by norm_num)
      exact this)
    intro v hv
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hv
    simp only [hs, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    rw [← QuotientGroup.mk_pow, hx, QuotientGroup.mk_one]
  have hfib : ∀ a ∈ s.image (QuotientGroup.mk : G → G ⧸ N),
      (s.filter (fun x => (QuotientGroup.mk x : G ⧸ N) = a)).card ≤ 2 := by
    intro a ha
    obtain ⟨x0, hx0, rfl⟩ := Finset.mem_image.1 ha
    calc (s.filter (fun x => (QuotientGroup.mk x : G ⧸ N) = QuotientGroup.mk x0)).card
        ≤ ((Finset.univ : Finset N).image (fun n : N => (n : G))).card := by
          refine Finset.card_le_card_of_injOn (fun y => x0⁻¹ * y) ?_ ?_
          · intro y hy
            have hy' : (QuotientGroup.mk y : G ⧸ N) = QuotientGroup.mk x0 := by
              simpa using (Finset.mem_filter.1 hy).2
            have : x0⁻¹ * y ∈ N := by
              rw [← QuotientGroup.eq]; exact hy'.symm
            simp only [Finset.coe_image, Finset.coe_univ, Set.image_univ, Set.mem_range,
              Subtype.exists, exists_prop, exists_eq_right]
            exact this
          · intro y _ z _ h
            simpa using h
      _ ≤ (Finset.univ : Finset N).card := Finset.card_image_le
      _ ≤ 2 := by rw [Finset.card_univ, ← Nat.card_eq_fintype_card]; exact hN
  calc s.card ≤ 2 * (s.image (QuotientGroup.mk : G → G ⧸ N)).card :=
        Finset.card_le_mul_card_image s 2 hfib
    _ ≤ 2 * 2 := by omega

/-- Powers of two: at most 4 elements of `(ZMod (2^e))ˣ` satisfy `u ^ ℓ = 1`, for prime `ℓ`
(1 for odd `ℓ`, at most 4 for `ℓ = 2`). -/
theorem card_torsion_units_two_pow_le (e ℓ : ℕ) (hℓ : ℓ.Prime) :
    Nat.card {u : (ZMod (2 ^ e))ˣ // u ^ ℓ = 1} ≤ 4 := by
  rcases eq_or_ne ℓ 2 with rfl | h2
  · have : NeZero (2 ^ e) := ⟨pow_ne_zero _ two_ne_zero⟩
    refine torsion_card_sq_le_four (Subgroup.zpowers (-1 : (ZMod (2 ^ e))ˣ)) ?_
    rw [Nat.card_zpowers]
    exact orderOf_le_of_pow_eq_one (by norm_num) (by simp)
  · rw [card_torsion_units_two_pow_odd e ℓ hℓ h2]; norm_num

end BachSharp
