import AbelianERH.Cyclotomic

/-!
# ERH for every subfield of a cyclotomic field, and for every abelian field

Let `L ⊇ ℚ` be a cyclotomic field `ℚ(ζ_N)`, `G = Gal(L/ℚ) ≅ (ℤ/N)ˣ` (`galEquivZMod`), `F` an
intermediate field, `H = Gal(L/F)` and `H_N ≤ (ℤ/N)ˣ` its image. `X(F)` is the set of Dirichlet
characters mod `N` trivial on `H_N` (Mathlib's `intermediateFieldEquivSubgroupChar`), and
`#X(F) = [F : ℚ]`.

* `sum_charsOf`: `∑_{χ ∈ X(F)} χ(a) = [F : ℚ] · [a ∈ H_N]` (orthogonality on `G/H_N`).
* `subfield_split`: for a prime `q ∤ N` with `u = q mod N`, every prime of `F` above `q` has the
  same inertia degree `f_F`, `#{𝔮 ∣ q} · f_F = [F : ℚ]` (`q` is unramified in `F`), and
  `f_F · #(H_N ∩ ⟨u⟩) = ord(u)`. The last identity comes from the tower `ℚ ⊆ F ⊆ L`: the inertia
  degrees multiply, `ord(u) = f_L`, and the relative degree `f(𝔔/𝔮)` is the order of the
  decomposition group of `𝔔` in `H`, which is `H ∩ ⟨Frob_q⟩` (Mathlib's
  `galEquivZMod_stabilizer`).
* `pow_mem_iff_dvd`: then `u^k ∈ H_N ⟺ f_F ∣ k` (`⟨u⟩ → G/H_N` has kernel `H_N ∩ ⟨u⟩`).
* `coeffIdentity_subfield`: hence `Λ_F(n) = ∑_{χ ∈ X(F)} χ(n) Λ(n)` for `n` coprime to `N`, and
  `extendedRiemannHypothesis_of_coeff` gives ERH for `F`.
* `dedekindZeta_congr`, `extendedRiemannHypothesis_of_algHom`: ERH transported along
  `K ≃ φ(K)` for `φ : K →ₐ[ℚ] ℚ(ζ_N)`; with Kronecker–Weber this covers every abelian `K`
  (`abelianERH_of_GRH`).
-/

namespace AbelianERH

open NumberField Finset ArithmeticFunction Artin.Analytic IsCyclotomicExtension.Rat
open scoped Pointwise

/-! ### Group theory -/

/-- In a finite commutative group, if `f · #(H ∩ ⟨u⟩) = ord(u)`, then `u^k ∈ H ⟺ f ∣ k`. -/
lemma pow_mem_iff_dvd {G : Type*} [CommGroup G] [Finite G] (Hz : Subgroup G) (u : G) {f : ℕ}
    (hf : f * Nat.card (Hz ⊓ Subgroup.zpowers u : Subgroup G) = orderOf u) (k : ℕ) :
    u ^ k ∈ Hz ↔ f ∣ k := by
  set C := Subgroup.zpowers u
  let φ : C →* G ⧸ Hz := (QuotientGroup.mk' Hz).comp C.subtype
  have hker : Nat.card φ.ker = Nat.card (Hz ⊓ C : Subgroup G) := by
    have : φ.ker = (Hz ⊓ C).subgroupOf C := by
      ext x
      simp [φ, Subgroup.mem_subgroupOf, QuotientGroup.eq_one_iff]
    rw [this]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv
  have hrange : Nat.card φ.range = orderOf (QuotientGroup.mk u : G ⧸ Hz) := by
    have : φ.range = Subgroup.zpowers (QuotientGroup.mk u : G ⧸ Hz) := by
      rw [MonoidHom.range_comp, Subgroup.range_subtype, MonoidHom.map_zpowers]
      rfl
    rw [this, Nat.card_zpowers]
  have h := Subgroup.card_ker_mul_card_range φ
  rw [hker, hrange, Nat.card_zpowers, ← hf, mul_comm f] at h
  have hpos : 0 < Nat.card (Hz ⊓ C : Subgroup G) := Nat.card_pos
  have hf' : orderOf (QuotientGroup.mk u : G ⧸ Hz) = f := Nat.eq_of_mul_eq_mul_left hpos h
  rw [← hf', orderOf_dvd_iff_pow_eq_one, ← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]

variable {N : ℕ} [NeZero N] {L : Type*} [Field L] [NumberField L] [IsCyclotomicExtension {N} ℚ L]
  [IsAbelianGalois ℚ L] (F : IntermediateField ℚ L)

/-! ### The characters of a subfield -/

variable (N) in
/-- The image `H_N ≤ (ℤ/N)ˣ` of `Gal(L/F)`. -/
noncomputable def unitsOf : Subgroup (ZMod N)ˣ :=
  (galEquivZMod N L).mapSubgroup F.fixingSubgroup

open Classical in
variable (N) in
/-- `X(F)`: the Dirichlet characters mod `N` trivial on `Gal(L/F)`. -/
noncomputable def charsOf : Finset (DirichletCharacter ℂ N) :=
  Finset.univ.filter (· ∈ intermediateFieldEquivSubgroupChar N L ℂ F)

lemma mem_charsOf {χ : DirichletCharacter ℂ N} :
    χ ∈ charsOf N F ↔ ∀ σ ∈ F.fixingSubgroup, χ (galEquivZMod N L σ) = 1 := by
  classical
  simp [charsOf]

lemma card_charsOf : (charsOf N F).card = Module.finrank ℚ F := by
  classical
  rw [← card_intermediateFieldEquivSubgroupChar N L ℂ F, Nat.card_eq_fintype_card,
    Fintype.card_subtype, charsOf]

lemma mem_unitsOf_iff (a : (ZMod N)ˣ) :
    a ∈ unitsOf N F ↔ ∀ χ ∈ charsOf N F, χ a = 1 := by
  constructor
  · intro ha χ hχ
    rw [unitsOf, MulEquiv.mapSubgroup_apply] at ha
    obtain ⟨σ, hσ, rfl⟩ := Subgroup.mem_map.1 ha
    exact (mem_charsOf F).1 hχ σ hσ
  · intro h
    have hY : (subgroupGalEquivSubgroupChar N L ℂ F.fixingSubgroup) =
        OrderDual.toDual (intermediateFieldEquivSubgroupChar N L ℂ F) := by
      apply OrderDual.ofDual.injective
      ext χ
      rw [mem_subgroupGalEquivSubgroupChar_iff, OrderDual.ofDual_toDual,
        mem_intermediateFieldEquivSubgroupChar_iff]
    have hσ : (galEquivZMod N L).symm a ∈ (subgroupGalEquivSubgroupChar N L ℂ).symm
        (OrderDual.toDual (intermediateFieldEquivSubgroupChar N L ℂ F)) := by
      rw [mem_subgroupGalEquivSubgroupChar_symm_iff]
      intro χ hχ
      rw [MulEquiv.apply_symm_apply]
      exact h χ (by classical simpa [charsOf] using hχ)
    rw [← hY, OrderIso.symm_apply_apply] at hσ
    rw [unitsOf, MulEquiv.mapSubgroup_apply]
    exact Subgroup.mem_map.2 ⟨_, hσ, by simp⟩

open Classical in
/-- **Orthogonality on `X(F)`.** -/
lemma sum_charsOf (a : (ZMod N)ˣ) :
    ∑ χ ∈ charsOf N F, χ a = if a ∈ unitsOf N F then (Module.finrank ℚ F : ℂ) else 0 := by
  classical
  by_cases ha : a ∈ unitsOf N F
  · rw [ite_eq_left ha, Finset.sum_congr rfl fun χ hχ => (mem_unitsOf_iff F a).1 ha χ hχ,
      Finset.sum_const, card_charsOf, nsmul_eq_mul, mul_one]
  rw [ite_eq_right ha]
  obtain ⟨χ₀, hχ₀, hne⟩ : ∃ χ₀ ∈ charsOf N F, χ₀ a ≠ 1 := by
    by_contra h
    push Not at h
    exact ha ((mem_unitsOf_iff F a).2 h)
  have hS : ∀ {χ}, χ ∈ charsOf N F ↔ χ ∈ intermediateFieldEquivSubgroupChar N L ℂ F :=
    fun {χ} => by simp [charsOf]
  have hmul : ∀ {χ}, χ ∈ charsOf N F → χ₀ * χ ∈ charsOf N F := fun {χ} hχ =>
    hS.2 (Subgroup.mul_mem _ (hS.1 hχ₀) (hS.1 hχ))
  have hinv : ∀ {χ}, χ ∈ charsOf N F → χ₀⁻¹ * χ ∈ charsOf N F := fun {χ} hχ =>
    hS.2 (Subgroup.mul_mem _ (Subgroup.inv_mem _ (hS.1 hχ₀)) (hS.1 hχ))
  have hsum : ∑ χ ∈ charsOf N F, χ a = χ₀ a * ∑ χ ∈ charsOf N F, χ a := by
    rw [Finset.mul_sum]
    refine Finset.sum_nbij' (fun χ => χ₀⁻¹ * χ) (fun χ => χ₀ * χ) (fun χ hχ => hinv hχ)
      (fun χ hχ => hmul hχ) (fun χ _ => by simp) (fun χ _ => by simp) fun χ _ => ?_
    rw [← MulChar.mul_apply, mul_inv_cancel_left]
  have : (1 - χ₀ a) * ∑ χ ∈ charsOf N F, χ a = 0 := by rw [sub_mul, one_mul, ← hsum, sub_self]
  exact (mul_eq_zero.1 this).resolve_left (sub_ne_zero.2 (Ne.symm hne))

/-! ### Splitting of `q ∤ N` in `F` -/

variable (N) in
/-- For `q ∤ N`: one inertia degree `f_F` above `q`, `#{𝔮 ∣ q} · f_F = [F : ℚ]`, and
`f_F · #(H_N ∩ ⟨q⟩) = ord_N(q)`. -/
lemma subfield_split {q : ℕ} (hq : q.Prime) (hcop : q.Coprime N) :
    (∀ P ∈ primesAbove F q, P.inertiaDeg ℤ = (Ideal.span {(q : ℤ)}).inertiaDegIn (𝓞 F)) ∧
    (primesAbove F q).card * (Ideal.span {(q : ℤ)}).inertiaDegIn (𝓞 F) =
      Module.finrank ℚ F ∧
    (Ideal.span {(q : ℤ)}).inertiaDegIn (𝓞 F) *
      Nat.card (unitsOf N F ⊓ Subgroup.zpowers (ZMod.unitOfCoprime q hcop) : Subgroup _) =
      orderOf (ZMod.unitOfCoprime q hcop) := by
  have := Fact.mk hq
  have := Int.ideal_span_isMaximal_of_prime q
  have hqN : ¬q ∣ N := (Nat.Prime.coprime_iff_not_dvd hq).1 hcop
  set p := Ideal.span {(q : ℤ)}
  set H := fixingSubgroup Gal(L/ℚ) (F : Set L)
  have : IsGaloisGroup H (𝓞 F) (𝓞 L) := IsGaloisGroup.of_isFractionRing _ (𝓞 F) (𝓞 L) F L
  have ha : ∀ P ∈ primesAbove F q, P.inertiaDeg ℤ = p.inertiaDegIn (𝓞 F) := fun P hP => by
    obtain ⟨h1, h2⟩ := (mem_primesAbove hq).1 hP
    exact (Ideal.inertiaDegIn_eq_inertiaDeg p P Gal(F/ℚ)).symm
  obtain ⟨⟨PF, hPF1, hPF2⟩⟩ := p.nonempty_primesOver (S := 𝓞 F)
  obtain ⟨⟨PL, hPL1, hPL2⟩⟩ := PF.nonempty_primesOver (S := 𝓞 L)
  have hPLp : PL.LiesOver p := Ideal.LiesOver.trans PL PF p
  have hPLmax : PL.IsMaximal := Ideal.primesOver.isMaximal (p := p) ⟨PL, hPL1, hPLp⟩
  have heL := IsCyclotomicExtension.Rat.ramificationIdxIn_eq_of_not_dvd q L hqN
  have hfL := IsCyclotomicExtension.Rat.inertiaDegIn_eq_of_not_dvd q L hqN
  have he := Ideal.ramificationIdxIn_mul_ramificationIdxIn (p := p) PF Gal(F/ℚ) (𝓞 L) Gal(L/ℚ) H
  have hf := Ideal.inertiaDegIn_mul_inertiaDegIn p PF Gal(F/ℚ) (𝓞 L) Gal(L/ℚ) H
  rw [heL] at he
  rw [hfL] at hf
  have heF : p.ramificationIdxIn (𝓞 F) = 1 := Nat.eq_one_of_mul_eq_one_right he
  have herel : PF.ramificationIdxIn (𝓞 L) = 1 := Nat.eq_one_of_mul_eq_one_left he
  refine ⟨ha, ?_, ?_⟩
  · have h := Ideal.ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn p (𝓞 F) Gal(F/ℚ)
    rw [heF, one_mul, ncard_primesOver_eq hq, IsGalois.card_aut_eq_finrank] at h
    exact h
  · have hst := Ideal.card_stabilizer_eq (G := H) PF PL
    rw [herel, one_mul] at hst
    have h1 : Nat.card (MulAction.stabilizer H PL) =
        Nat.card (H ⊓ MulAction.stabilizer Gal(L/ℚ) PL : Subgroup _) :=
      Nat.card_congr
        { toFun := fun x => ⟨x.1.1, x.1.2, x.2⟩
          invFun := fun x => ⟨⟨x.1, x.2.1⟩, x.2.2⟩
          left_inv := fun _ => rfl
          right_inv := fun _ => rfl }
    have h2 := galEquivZMod_stabilizer N L q PL hcop
    replace hst := h1.symm.trans hst
    rw [← Subgroup.card_map_of_injective (f := (galEquivZMod N L).toMonoidHom)
      (galEquivZMod N L).injective, Subgroup.map_inf_eq _ _ (galEquivZMod N L).toMonoidHom (galEquivZMod N L).injective]
      at hst
    rw [MulEquiv.mapSubgroup_apply] at h2
    have hord : orderOf (q : ZMod N) = orderOf (ZMod.unitOfCoprime q hcop) := by
      rw [← orderOf_injective _ Units.coeHom_injective, Units.coeHom_apply,
        ZMod.coe_unitOfCoprime]
    rw [← hord, ← hf, ← hst, unitsOf, MulEquiv.mapSubgroup_apply, ← h2]
    rfl

/-- **The coefficient identity for a subfield `F` of `ℚ(ζ_N)`**:
`Λ_F(n) = ∑_{χ ∈ X(F)} χ(n) Λ(n)` for `(n, N) = 1`. -/
theorem coeffIdentity_subfield : CoeffIdentity F (charsOf N F) := by
  classical
  intro n hn
  rw [← Finset.sum_mul]
  by_cases hΛ : Λ n = 0
  · simp [hΛ, vonMangoldtK_eq_zero F hΛ]
  obtain ⟨q, k, hq, hk, rfl⟩ := (isPrimePow_nat_iff n).1 (vonMangoldt_ne_zero_iff.1 hΛ)
  have hcop : q.Coprime N := Nat.Coprime.coprime_dvd_left (dvd_pow_self q hk.ne') hn
  obtain ⟨hf, hcard, hrel⟩ := subfield_split N F hq hcop
  have hcast : ((q ^ k : ℕ) : ZMod N) = ((ZMod.unitOfCoprime q hcop ^ k : (ZMod N)ˣ) : ZMod N) := by
    rw [Units.val_pow_eq_pow_val, ZMod.coe_unitOfCoprime, Nat.cast_pow]
  rw [vonMangoldtK_prime_pow F hq hf hcard hk, vonMangoldt_apply_pow hk.ne',
    vonMangoldt_apply_prime hq, hcast, sum_charsOf]
  have hiff := pow_mem_iff_dvd _ _ hrel k
  by_cases h : (Ideal.span {(q : ℤ)}).inertiaDegIn (𝓞 F) ∣ k
  · rw [ite_eq_left h, ite_eq_left (hiff.2 h)]
    push_cast
    ring
  · rw [ite_eq_right h, ite_eq_right (mt hiff.1 h)]
    simp

include N in
omit [IsAbelianGalois ℚ L] in
/-- **ERH for every subfield of `ℚ(ζ_N)`, from GRH for Dirichlet L-functions.** -/
theorem subfield_extendedRiemannHypothesis_of_GRH (hGRH : DirichletLZerosOnLine) :
    ERH.ExtendedRiemannHypothesis F := by
  have : IsAbelianGalois ℚ L := IsCyclotomicExtension.isAbelianGalois {N} ℚ L
  exact extendedRiemannHypothesis_of_coeff F hGRH (coeffIdentity_subfield (N := N) F)

/-! ### Transport and Kronecker–Weber -/

section Transport

variable {K K' : Type*} [Field K] [NumberField K] [Field K'] [NumberField K']

/-- `ζ_K` depends only on the isomorphism class of `K`: ideals correspond under `𝓞 K ≃ 𝓞 K'`,
with the same norm (the quotients are isomorphic). -/
lemma dedekindZeta_congr (e : K ≃+* K') : dedekindZeta K = dedekindZeta K' := by
  funext s
  simp only [dedekindZeta]
  congr 1
  funext n
  congr 1
  let e' := NumberField.RingOfIntegers.mapRingEquiv e
  have hnorm : ∀ I : Ideal (𝓞 K), Ideal.absNorm (I.map (e' : 𝓞 K →+* 𝓞 K')) = Ideal.absNorm I :=
    fun I => by
      rw [Ideal.absNorm_apply, Ideal.absNorm_apply, Submodule.cardQuot_apply,
        Submodule.cardQuot_apply]
      exact (Nat.card_congr (Ideal.quotientEquiv I _ e' rfl).toEquiv).symm
  have hnorm' : ∀ J : Ideal (𝓞 K'),
      Ideal.absNorm (J.map (e'.symm : 𝓞 K' →+* 𝓞 K)) = Ideal.absNorm J :=
    fun J => by
      rw [Ideal.absNorm_apply, Ideal.absNorm_apply, Submodule.cardQuot_apply,
        Submodule.cardQuot_apply]
      exact (Nat.card_congr (Ideal.quotientEquiv J _ e'.symm rfl).toEquiv).symm
  exact Nat.card_congr
    { toFun := fun I => ⟨I.1.map (e' : 𝓞 K →+* 𝓞 K'), (hnorm I.1).trans I.2⟩
      invFun := fun J => ⟨J.1.map (e'.symm : 𝓞 K' →+* 𝓞 K), (hnorm' J.1).trans J.2⟩
      left_inv := fun I => Subtype.ext (Ideal.map_of_equiv e')
      right_inv := fun J => Subtype.ext (Ideal.map_of_equiv e'.symm) }

/-- ERH is invariant under isomorphism. -/
lemma extendedRiemannHypothesis_congr (e : K ≃+* K') (h : ERH.ExtendedRiemannHypothesis K') :
    ERH.ExtendedRiemannHypothesis K := fun Z hZ =>
  h Z ⟨hZ.1, fun s hs => (hZ.2 s hs).trans (by rw [dedekindZeta_congr e])⟩

end Transport

/-- **ERH for every field that embeds in a cyclotomic field, from GRH** (tier C). -/
theorem extendedRiemannHypothesis_of_algHom (hGRH : DirichletLZerosOnLine) (K : Type*) [Field K]
    [NumberField K] {N : ℕ} [NeZero N] (φ : K →ₐ[ℚ] CyclotomicField N ℚ) :
    ERH.ExtendedRiemannHypothesis K := by
  have : NeZero ((N : ℕ) : ℚ) := ⟨by exact_mod_cast NeZero.ne N⟩
  have : IsCyclotomicExtension {N} ℚ (CyclotomicField N ℚ) := CyclotomicField.isCyclotomicExtension N ℚ
  exact extendedRiemannHypothesis_congr (AlgEquiv.ofInjectiveField φ).toRingEquiv
    (subfield_extendedRiemannHypothesis_of_GRH (N := N) φ.fieldRange hGRH)

/-- **Headline (tier C + H).** ERH for every finite abelian extension of `ℚ`, from GRH for
Dirichlet L-functions and the Kronecker–Weber theorem. -/
theorem abelianERH_of_GRH (hGRH : DirichletLZerosOnLine) (hKW : KroneckerWeberStatement) :
    AbelianERHStatement := fun K _ _ _ => by
  obtain ⟨N, hN, ⟨φ⟩⟩ := hKW K
  have : NeZero N := ⟨hN.ne'⟩
  exact extendedRiemannHypothesis_of_algHom hGRH K φ

end AbelianERH
