import Artin.Analytic.Interface

/-!
# The discriminant of a Kummer field (blueprint step A6)

`log |d_{K_k}| ≤ 4 [K_k : ℚ] log(k |a|)`.

Serre's bound `log |d_K| ≤ (n - 1) ∑_{p ramified} log p + n log n` needs the exponent bound for
the different, which Mathlib lacks. We use Hadamard's inequality instead. The products
`ζ^i α^j` (`i, j < k`, `ζ` a primitive `k`-th root of unity, `α^k = a`) span `K_k` over `ℚ`, so
some of them form a `ℚ`-basis `B` of algebraic integers. Its discriminant is a nonzero integer
multiple of `d_K` (the change of basis from an integral basis has integer entries), and it is
`det(σ(B_i))²` over the `n` embeddings `σ : K → ℂ`. Every entry has absolute value at most
`|a|`, so `|det| ≤ n! |a|^n` (`Matrix.det_le`), and `n ≤ k φ(k) ≤ k²`.

Main results:

* `abs_discr_le_of_basis`: `|d_K| ≤ |disc B|` for a `ℚ`-basis `B` of algebraic integers, in any
  number field;
* `log_abs_discr_le`: `log |d_{K_k}| ≤ 4 [K_k : ℚ] log(k |a|)`.
-/

namespace Artin.Analytic

open Polynomial NumberField Artin.Kummer Module

section General

variable {K : Type*} [Field K] [NumberField K]

/-- The discriminant of a `ℚ`-basis of `K` made of algebraic integers is a nonzero integer
square times `d_K`, so `|d_K| ≤ |disc B|`. -/
lemma abs_discr_le_of_basis {ι : Type*} [Fintype ι] [DecidableEq ι] (B : Basis ι ℚ K)
    (hB : ∀ i, IsIntegral ℤ (B i)) : |(discr K : ℚ)| ≤ |Algebra.discr ℚ B| := by
  classical
  set e := (integralBasis K).indexEquiv B
  have hint : ∀ i j, IsIntegral ℤ (((integralBasis K).reindex e).toMatrix B i j) := by
    intro i j
    rw [Basis.toMatrix_apply, Basis.repr_reindex_apply]
    obtain ⟨x, hx⟩ : ∃ x : 𝓞 K, algebraMap (𝓞 K) K x = B j :=
      ⟨(⟨B j, (mem_integralClosure_iff ℤ K).2 (hB j)⟩ : 𝓞 K), rfl⟩
    rw [← hx, integralBasis_repr_apply]
    exact isIntegral_algebraMap
  have hd : Algebra.discr ℚ B =
      (((integralBasis K).reindex e).toMatrix B).det ^ 2 * Algebra.discr ℚ (integralBasis K) := by
    conv_lhs => rw [← ((integralBasis K).reindex e).toMatrix_map_vecMul B]
    rw [Algebra.discr_of_matrix_vecMul, Basis.coe_reindex, Algebra.discr_reindex]
  obtain ⟨r, hr⟩ := IsIntegrallyClosed.isIntegral_iff.1 (IsIntegral.det fun i j => hint i j)
  rw [← hr, ← coe_discr] at hd
  have hB0 := Algebra.discr_not_zero_of_basis ℚ B
  have hr0 : r ≠ 0 := by
    rintro rfl; apply hB0; rw [hd]; simp
  rw [hd, abs_mul, abs_pow]
  have h1 : (1 : ℚ) ≤ |(algebraMap ℤ ℚ r)| ^ 2 := by
    have : (1 : ℚ) ≤ |(r : ℚ)| := by exact_mod_cast Int.one_le_abs hr0
    simpa using one_le_pow₀ (n := 2) this
  calc |(discr K : ℚ)| = 1 * |(discr K : ℚ)| := (one_mul _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_right h1 (abs_nonneg _)

/-- Hadamard: if every conjugate of every element of a `ℚ`-basis `B` of `K` has absolute value at
most `M`, then `|disc B| ≤ (n! M^n)²`. -/
lemma abs_discr_le_of_norm_le {ι : Type*} [Fintype ι] [DecidableEq ι] (B : Basis ι ℚ K) {M : ℝ}
    (hM : ∀ i (σ : K →ₐ[ℚ] ℂ), ‖σ (B i)‖ ≤ M) :
    |(Algebra.discr ℚ B : ℝ)| ≤ ((Fintype.card ι).factorial * M ^ Fintype.card ι) ^ 2 := by
  classical
  have hcard : Fintype.card ι = Fintype.card (K →ₐ[ℚ] ℂ) := by
    rw [AlgHom.card, ← finrank_eq_card_basis B]
  set e := Fintype.equivOfCardEq hcard
  have h := Algebra.discr_eq_det_embeddingsMatrixReindex_pow_two ℚ ℂ B e
  have hdet : ‖(Algebra.embeddingsMatrixReindex ℚ ℂ B e).det‖ ≤
      (Fintype.card ι).factorial • M ^ Fintype.card ι := by
    have := Matrix.det_le (abv := NormedField.toAbsoluteValue ℂ)
      (A := Algebra.embeddingsMatrixReindex ℚ ℂ B e) (x := M) (fun i j => by
        simpa [Algebra.embeddingsMatrixReindex, Algebra.embeddingsMatrix] using hM i (e j))
    simpa using this
  have h1 : |(Algebra.discr ℚ B : ℝ)| = ‖(Algebra.embeddingsMatrixReindex ℚ ℂ B e).det‖ ^ 2 := by
    rw [← norm_pow, ← h]
    simp
  rw [h1, nsmul_eq_mul] at *
  exact pow_le_pow_left₀ (norm_nonneg _) hdet 2

end General

/-! ### The monomials `ζ^i α^j` span -/

section Span

variable {L : Type*} [Field L] [Algebra ℚ L] {a : ℤ} {k : ℕ}

open Classical in
/-- The products `ζ^i α^j` with `i, j < k`. -/
noncomputable def monomials (ζ α : L) (k : ℕ) : Finset L :=
  (Finset.range k ×ˢ Finset.range k).image fun ij => ζ ^ ij.1 * α ^ ij.2

omit [Algebra ℚ L] in
lemma mem_monomials {ζ α x : L} :
    x ∈ monomials ζ α k ↔ ∃ i < k, ∃ j < k, ζ ^ i * α ^ j = x := by
  classical
  simp only [monomials, Finset.mem_image, Finset.mem_product, Finset.mem_range, Prod.exists]
  constructor
  · rintro ⟨i, j, ⟨hi, hj⟩, h⟩; exact ⟨i, hi, j, hj, h⟩
  · rintro ⟨i, hi, j, hj, h⟩; exact ⟨i, j, ⟨hi, hj⟩, h⟩

lemma pow_mul_pow_mem_span {ζ α : L} (hζ : ζ ^ k = 1) (hα : α ^ k = a) (hk : k ≠ 0) (i j : ℕ) :
    ζ ^ i * α ^ j ∈ Submodule.span ℚ (monomials ζ α k : Set L) := by
  have hi : ζ ^ i = ζ ^ (i % k) := by
    conv_lhs => rw [← Nat.div_add_mod i k, pow_add, pow_mul, hζ, one_pow, one_mul]
  have hj : α ^ j = (a : L) ^ (j / k) * α ^ (j % k) := by
    conv_lhs => rw [← Nat.div_add_mod j k, pow_add, pow_mul, hα]
  have hmem : ζ ^ (i % k) * α ^ (j % k) ∈ (monomials ζ α k : Set L) := by
    rw [Finset.mem_coe, mem_monomials]
    exact ⟨_, Nat.mod_lt _ (Nat.pos_of_ne_zero hk), _, Nat.mod_lt _ (Nat.pos_of_ne_zero hk), rfl⟩
  have : ζ ^ i * α ^ j = ((a : ℚ) ^ (j / k)) • (ζ ^ (i % k) * α ^ (j % k)) := by
    rw [Algebra.smul_def, map_pow, map_intCast, hi, hj]; ring
  rw [this]
  exact Submodule.smul_mem _ _ (Submodule.subset_span hmem)

lemma mul_mem_span {ζ α : L} (hζ : ζ ^ k = 1) (hα : α ^ k = a) (hk : k ≠ 0) {x y : L}
    (hx : x ∈ Submodule.span ℚ (monomials ζ α k : Set L))
    (hy : y ∈ Submodule.span ℚ (monomials ζ α k : Set L)) :
    x * y ∈ Submodule.span ℚ (monomials ζ α k : Set L) := by
  have := Submodule.mul_mem_mul hx hy
  rw [Submodule.span_mul_span] at this
  refine Submodule.span_le.2 ?_ this
  intro z hz
  obtain ⟨s, hs, t, ht, rfl⟩ := Set.mem_mul.1 hz
  obtain ⟨i, -, j, -, rfl⟩ := mem_monomials.1 hs
  obtain ⟨i', -, j', -, rfl⟩ := mem_monomials.1 ht
  have : ζ ^ i * α ^ j * (ζ ^ i' * α ^ j') = ζ ^ (i + i') * α ^ (j + j') := by ring
  rw [this]
  exact pow_mul_pow_mem_span hζ hα hk _ _

/-- If the roots `ζ^i α` of `X^k - a` generate `L` as a `ℚ`-algebra, the monomials span `L`. -/
lemma span_monomials_eq_top {ζ α : L} (hζ : ζ ^ k = 1) (hα : α ^ k = a) (hk : k ≠ 0) {R : Set L}
    (hR : Algebra.adjoin ℚ R = ⊤) (hRmem : ∀ x ∈ R, ∃ i, x = ζ ^ i * α) :
    Submodule.span ℚ (monomials ζ α k : Set L) = ⊤ := by
  rw [eq_top_iff]
  suffices h : ∀ x ∈ Algebra.adjoin ℚ R, x ∈ Submodule.span ℚ (monomials ζ α k : Set L) from
    fun x _ => h x (by rw [hR]; trivial)
  intro x hx
  induction hx using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨i, rfl⟩ := hRmem x hx
    simpa using pow_mul_pow_mem_span hζ hα hk i 1
  | algebraMap r =>
    have := Submodule.smul_mem (Submodule.span ℚ (monomials ζ α k : Set L)) r
      (pow_mul_pow_mem_span hζ hα hk 0 0)
    simpa [Algebra.smul_def] using this
  | add x y _ _ hx hy => exact Submodule.add_mem _ hx hy
  | mul x y _ _ hx hy => exact mul_mem_span hζ hα hk hx hy

omit [Algebra ℚ L] in
lemma isIntegral_of_mem_monomials {ζ α x : L} (hζ : ζ ^ k = 1) (hα : α ^ k = a) (hk : k ≠ 0)
    (hx : x ∈ monomials ζ α k) : IsIntegral ℤ x := by
  obtain ⟨i, -, j, -, rfl⟩ := mem_monomials.1 hx
  have h1 : IsIntegral ℤ ζ := IsIntegral.of_pow (Nat.pos_of_ne_zero hk) (hζ ▸ isIntegral_one)
  have h2 : IsIntegral ℤ α :=
    IsIntegral.of_pow (Nat.pos_of_ne_zero hk) (hα ▸ isIntegral_algebraMap (x := a))
  exact (h1.pow i).mul (h2.pow j)

lemma pow_le_of_pow_eq {t A : ℝ} (ht : 0 ≤ t) (hA : 1 ≤ A) (htk : t ^ k = A) {j : ℕ}
    (hj : j < k) : t ^ j ≤ A := by
  rcases le_or_gt t 1 with h | h
  · exact (pow_le_one₀ ht h).trans hA
  · rw [← htk]; exact pow_le_pow_right₀ h.le hj.le

lemma norm_le_of_mem_monomials {ζ α x : L} (hζ : ζ ^ k = 1) (hα : α ^ k = a) (hk : k ≠ 0)
    (ha : a ≠ 0) (σ : L →ₐ[ℚ] ℂ) (hx : x ∈ monomials ζ α k) : ‖σ x‖ ≤ |(a : ℝ)| := by
  obtain ⟨i, -, j, hj, rfl⟩ := mem_monomials.1 hx
  have hζ1 : ‖σ ζ‖ = 1 :=
    Complex.norm_eq_one_of_pow_eq_one (by rw [← map_pow, hζ, map_one]) hk
  have hαk : ‖σ α‖ ^ k = |(a : ℝ)| := by
    rw [← norm_pow, ← map_pow, hα, map_intCast, Complex.norm_intCast]
  have hA : (1 : ℝ) ≤ |(a : ℝ)| := by exact_mod_cast Int.one_le_abs ha
  rw [map_mul, map_pow, map_pow, norm_mul, norm_pow, norm_pow, hζ1, one_pow, one_mul]
  exact pow_le_of_pow_eq (norm_nonneg _) hA hαk hj

end Span

/-! ### The Kummer field -/

section KField

variable {a : ℤ} {k : ℕ}

/-- `|d_{K_k}| ≤ (n! |a|^n)²` with `n = [K_k : ℚ]`. -/
theorem abs_discr_le (ha : a ≠ 0) (hk : k ≠ 0) :
    |(discr (KField a k) : ℝ)| ≤
      ((kummerDegree a k).factorial * |(a : ℝ)| ^ kummerDegree a k) ^ 2 := by
  classical
  obtain ⟨α, hα⟩ := exists_root ha hk
  obtain ⟨ζ, hζ⟩ := exists_isPrimitiveRoot ha hk
  have hα0 : α ≠ 0 := by
    rintro rfl; rw [zero_pow hk] at hα; exact ha (by exact_mod_cast hα.symm)
  have hspan := span_monomials_eq_top hζ.pow_eq_one hα hk (SplittingField.adjoin_rootSet _)
    (fun x hx => by
      rw [mem_rootSet_iff hk] at hx
      have : NeZero k := ⟨hk⟩
      obtain ⟨i, -, hi⟩ := hζ.eq_pow_of_pow_eq_one (ξ := x / α) (by
        rw [div_pow, hx, hα, div_self (by exact_mod_cast ha)])
      exact ⟨i, by rw [hi, div_mul_cancel₀ _ hα0]⟩)
  obtain ⟨b, hbS, hbspan, hli⟩ :=
    exists_linearIndependent ℚ (monomials ζ α k : Set (KField a k))
  have : Fintype b := ((monomials ζ α k).finite_toSet.subset hbS).fintype
  let B := Basis.mk hli (by rw [Subtype.range_coe, hbspan, hspan])
  have hBmem : ∀ i, B i ∈ monomials ζ α k := fun i => by rw [Basis.mk_apply]; exact hbS i.2
  have hcard : Fintype.card b = kummerDegree a k := (finrank_eq_card_basis B).symm
  have h1 := abs_discr_le_of_basis B fun i =>
    isIntegral_of_mem_monomials hζ.pow_eq_one hα hk (hBmem i)
  have h2 := abs_discr_le_of_norm_le B (M := |(a : ℝ)|) fun i σ =>
    norm_le_of_mem_monomials hζ.pow_eq_one hα hk ha σ (hBmem i)
  rw [hcard] at h2
  calc |(discr (KField a k) : ℝ)| = ((|(discr (KField a k) : ℚ)| : ℚ) : ℝ) := by push_cast; rfl
    _ ≤ ((|Algebra.discr ℚ B| : ℚ) : ℝ) := by exact_mod_cast h1
    _ = |(Algebra.discr ℚ B : ℝ)| := by push_cast; rfl
    _ ≤ _ := h2

/-- **A6.** `log |d_{K_k}| ≤ 4 [K_k : ℚ] log(k |a|)`. -/
theorem log_abs_discr_le (ha : a ≠ 0) (hk : k ≠ 0) :
    Real.log |(discr (KField a k) : ℝ)| ≤ 4 * kummerDegree a k * Real.log (k * |(a : ℝ)|) := by
  set n := kummerDegree a k
  set A := |(a : ℝ)|
  have hA : 1 ≤ A := by
    have : ((1 : ℤ) : ℝ) ≤ ((|a| : ℤ) : ℝ) := by exact_mod_cast Int.one_le_abs ha
    simpa [A] using this
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast Nat.one_le_iff_ne_zero.2 hk
  have hn : (n : ℝ) ≤ (k : ℝ) ^ 2 := by
    have := kummerDegree_le ha hk
    have h2 : k * k.totient ≤ k ^ 2 := by
      rw [pow_two]; exact Nat.mul_le_mul_left _ (Nat.totient_le k)
    exact_mod_cast this.trans h2
  have hd0 : 0 < |(discr (KField a k) : ℝ)| := by
    have := discr_ne_zero (KField a k)
    positivity
  have hbound : |(discr (KField a k) : ℝ)| ≤ (k * A) ^ (4 * n) := by
    refine (abs_discr_le ha hk).trans ?_
    have hfac : (n.factorial : ℝ) ≤ ((k : ℝ) ^ 2) ^ n := by
      have : (n.factorial : ℝ) ≤ (n : ℝ) ^ n := by exact_mod_cast Nat.factorial_le_pow n
      exact this.trans (pow_le_pow_left₀ (Nat.cast_nonneg _) hn n)
    have hA2 : A ^ n ≤ A ^ (2 * n) := pow_le_pow_right₀ hA (by omega)
    calc ((n.factorial : ℝ) * A ^ n) ^ 2 ≤ (((k : ℝ) ^ 2) ^ n * A ^ (2 * n)) ^ 2 := by
          gcongr
      _ = (k * A) ^ (4 * n) := by ring
  have := Real.log_le_log hd0 hbound
  rw [Real.log_pow] at this
  push_cast at this
  linarith

end KField

end Artin.Analytic
