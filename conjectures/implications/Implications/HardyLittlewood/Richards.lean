import Implications.HardyLittlewood.Statement
import Implications.HardyLittlewood.Tuple

/-!
# Richards' theorem: the two Hardy–Littlewood conjectures are incompatible

Hensley and Richards (*Acta Arith.* 25 (1973/74), 375–391) and Richards (*Bull. Amer. Math.
Soc.* 80 (1974), 419–438) showed that the first Hardy–Littlewood conjecture (the prime
`k`-tuples conjecture with the Hardy–Littlewood constant) contradicts the second,
`π(x + y) ≤ π(x) + π(y)`. This file proves formal-conjectures'
`HardyLittlewood.not_first_and_secondHardyLittlewoodConjecture`, with its statement unchanged.

Proof.

1. `tuple` (`Implications.HardyLittlewood.Tuple`) is an admissible 447-tuple
   `0 = m₀ < ⋯ < m₄₄₆ = 3158` of even numbers, while `π(3159) = 446`.
2. Its Hardy–Littlewood constant is positive (`constant_pos`): every factor is positive because
   the tuple misses a class mod every prime, and for `q > 3158` the factor
   `(1 - 447/q)/(1 - 1/q)^447` is within `2·447²/q²` of `1` (`factor_sub_one_le`), so the logs of
   the factors are summable and the product is the exponential of their sum.
3. The integral `∫ t in 2..n, 1/log t ^ 447` is positive for `n ≥ 3`, so the first conjecture
   makes the counting function of the constellation eventually nonzero: some `p` has all 447
   numbers `p + mᵢ` prime (`exists_constellation`).
4. These are 447 primes in `[p, p + 3158]`, so `π(p - 1 + 3159) ≥ π(p - 1) + 447`, while the
   second conjecture at `x = p - 1 ≥ 2`, `y = 3159` gives at most `π(p - 1) + 446`.
-/

open Asymptotics Filter

open scoped Nat.Prime

namespace HardyLittlewood.Richards

/-- The 447-tuple as a function on `Fin 447`. -/
def m : Fin (Nat.succ 446) → ℕ := fun i => tuple.get (Fin.cast tuple_length.symm i)

lemma tuple_pairwise : tuple.Pairwise (· < ·) := List.isChain_iff_pairwise.mp tuple_chain

lemma tuple_nodup : tuple.Nodup := tuple_pairwise.imp fun h => ne_of_lt h

lemma m_mem (i : Fin (Nat.succ 446)) : m i ∈ tuple := List.get_mem _ _

lemma mem_tuple_iff (x : ℕ) : x ∈ tuple ↔ ∃ i, m i = x := by
  rw [List.mem_iff_get]
  constructor
  · rintro ⟨j, rfl⟩
    exact ⟨Fin.cast tuple_length j, by simp [m]⟩
  · rintro ⟨i, rfl⟩
    exact ⟨Fin.cast tuple_length.symm i, rfl⟩

lemma even_le_of_mem {x : ℕ} (hx : x ∈ tuple) : x % 2 = 0 ∧ x ≤ 3158 := by
  have := List.all_eq_true.mp tuple_even_le x hx
  simpa using this

lemma m_zero : m 0 = 0 := rfl

lemma m_one : m 1 = 2 := rfl

lemma m_injective : Function.Injective m := by
  intro i j h
  have := (List.nodup_iff_injective_get.mp tuple_nodup) h
  exact Fin.cast_injective _ this

lemma m_even (i : Fin (Nat.succ 446)) : Even (m i) :=
  Nat.even_iff.mpr (even_le_of_mem (m_mem i)).1

lemma m_le (i : Fin (Nat.succ 446)) : m i ≤ 3158 := (even_le_of_mem (m_mem i)).2

/-- For `2 ≤ q ≤ 447` some residue class mod `q` contains no `mᵢ`. -/
lemma exists_missing (q : ℕ) (hq2 : 2 ≤ q) (hq : q ≤ 447) :
    ∃ r < q, ∀ i, m i % q ≠ r := by
  have hj : q - 2 < ((List.range' 2 446).zip witness).length := by
    simp [witness_length]; omega
  have hmem := List.getElem_mem hj
  have h := List.all_eq_true.mp witness_ok _ hmem
  simp only [List.getElem_zip, List.getElem_range', Bool.and_eq_true, decide_eq_true_eq,
    List.all_eq_true, bne_iff_ne, ne_eq, one_mul] at h
  have hq' : 2 + (q - 2) = q := by omega
  rw [hq'] at h
  refine ⟨_, h.1, fun i => h.2 _ (m_mem i)⟩

/-- The number of classes mod `q` met by the tuple is below `q`, for every prime `q`. -/
lemma numResidues_lt (q : ℕ) (hq : q.Prime) : Nat.numResidues q m < q := by
  have : NeZero q := ⟨hq.ne_zero⟩
  unfold Nat.numResidues
  rcases le_or_gt q 447 with hle | hgt
  · obtain ⟨r, hr, hmiss⟩ := exists_missing q hq.two_le hle
    have hne : Set.range (fun i => (m i : ZMod q)) ≠ Set.univ := by
      intro h
      obtain ⟨i, hi⟩ := (Set.eq_univ_iff_forall.mp h) (r : ZMod q)
      have := (ZMod.natCast_eq_natCast_iff' _ _ _).mp hi
      rw [Nat.mod_eq_of_lt hr] at this
      exact hmiss i this
    calc _ < Nat.card (ZMod q) := Set.ncard_lt_card hne
      _ = q := Nat.card_zmod q
  · calc _ ≤ (Set.univ : Set (Fin (Nat.succ 446))).ncard := by
          rw [← Set.image_univ]; exact Set.ncard_image_le (Set.toFinite _)
      _ = 447 := by simp
      _ < q := hgt

/-- For `q > 3158` the 447 entries lie in distinct classes. -/
lemma numResidues_eq (q : ℕ) (hq : 3158 < q) : Nat.numResidues q m = 447 := by
  unfold Nat.numResidues
  have hinj : Function.Injective (fun i => (m i : ZMod q)) := by
    intro i j h
    have := (ZMod.natCast_eq_natCast_iff' _ _ _).mp h
    rw [Nat.mod_eq_of_lt (by have := m_le i; omega),
      Nat.mod_eq_of_lt (by have := m_le j; omega)] at this
    exact m_injective this
  rw [Set.ncard_range_of_injective hinj]
  simp

/-! ### The analytic part, for a general tuple

Everything below is stated for an arbitrary `t : Fin k.succ → ℕ`, with the arithmetic input as
hypotheses; it is applied to `m` (with `k = 446`) only at the end. -/

/-- The elementary estimate behind the convergence of the singular series:
`|(1 - n x)/(1 - x)^n - 1| ≤ 2 n² x²` when `0 < x` and `n x ≤ 1/2`. -/
lemma factor_sub_one_le (n : ℕ) (x : ℝ) (hx0 : 0 < x) (hx1' : x ≤ 1)
    (hx1 : (n : ℝ) * x ≤ 1 / 2) :
    |(1 - n * x) / (1 - x) ^ n - 1| ≤ 2 * (n : ℝ) ^ 2 * x ^ 2 := by
  have hnx : 0 ≤ (n : ℝ) * x := mul_nonneg (Nat.cast_nonneg n) hx0.le
  obtain ⟨P, hP⟩ : ∃ P : ℝ, P = (1 - x) ^ n := ⟨_, rfl⟩
  rw [← hP]
  have hlow : 1 - n * x ≤ P := by
    have h := one_add_mul_le_pow (a := -x) (by linarith) n
    rw [← sub_eq_add_neg, ← hP] at h
    linarith
  have hup : P ≤ 1 - n * x + (n * x) ^ 2 := by
    have h1 : P ≤ Real.exp (-x) ^ n := by
      rw [hP]
      exact pow_le_pow_left₀ (by linarith) (Real.one_sub_le_exp_neg x) n
    have h2 : Real.exp (-x) ^ n = Real.exp (-(n * x)) := by
      rw [← Real.exp_nat_mul]; congr 1; ring
    have h3 := Real.abs_exp_sub_one_sub_id_le (x := -(n * x))
      (by rw [abs_neg, abs_of_nonneg hnx]; linarith)
    have h4 := (abs_le.mp h3).2
    rw [neg_sq] at h4
    linarith
  have hP0 : 0 < P := by linarith
  rw [div_sub_one hP0.ne', abs_div, abs_of_pos hP0, div_le_iff₀ hP0,
    abs_of_nonpos (by linarith)]
  nlinarith [mul_nonneg (mul_nonneg (sq_nonneg (n : ℝ)) (sq_nonneg x))
    (by linarith : (0 : ℝ) ≤ 2 * P - 1)]

/-- The same estimate at `x = 1/q`. -/
lemma factor_sub_one_le' (n : ℕ) (q : ℝ) (hq : 2 * (n : ℝ) ≤ q) (hq1 : 1 ≤ q) :
    |(1 - (n : ℝ) / q) / (1 - 1 / q) ^ n - 1| ≤ 2 * (n : ℝ) ^ 2 * (1 / q ^ 2) := by
  have hq0 : 0 < q := by linarith
  have h := factor_sub_one_le n (1 / q) (by positivity) (by rw [div_le_one hq0]; exact hq1)
    (by rw [mul_one_div, div_le_iff₀ hq0]; linarith)
  rwa [mul_one_div, one_div_pow] at h

/-- A product of Hardy–Littlewood factors is positive when the tuple misses a class mod every
prime and occupies `k + 1` distinct classes mod every large prime. -/
lemma tprod_pos {k : ℕ} (t : Fin k.succ → ℕ) (B : ℕ)
    (hlt : ∀ q : ℕ, q.Prime → Nat.numResidues q t < q)
    (heq : ∀ q : ℕ, B < q → Nat.numResidues q t = k.succ) :
    0 < ∏' (q : { q : ℕ // q.Prime ∧ 3 ≤ q}),
        (1 - (Nat.numResidues q t : ℝ) / q) / (1 - 1 / q) ^ k.succ := by
  set f : { q : ℕ // q.Prime ∧ 3 ≤ q} → ℝ :=
    fun q => (1 - (Nat.numResidues q t : ℝ) / q) / (1 - 1 / q) ^ k.succ with hf
  have hpos : ∀ q, 0 < f q := by
    intro q
    have hq3 : (3 : ℝ) ≤ (q : ℕ) := by exact_mod_cast q.2.2
    have hl : (Nat.numResidues q t : ℝ) < (q : ℕ) := by exact_mod_cast hlt q q.2.1
    apply div_pos
    · rw [sub_pos, div_lt_one (by linarith)]; exact hl
    · apply pow_pos
      rw [sub_pos, div_lt_one (by linarith)]; linarith
  have hg : Summable fun q => f q - 1 := by
    have hs : Summable fun q : { q : ℕ // q.Prime ∧ 3 ≤ q} =>
        2 * ((k.succ : ℕ) : ℝ) ^ 2 * (1 / ((q : ℕ) : ℝ) ^ 2) :=
      ((Real.summable_one_div_nat_pow.mpr one_lt_two).comp_injective
        Subtype.val_injective).mul_left _
    refine hs.of_norm_bounded_eventually ?_
    rw [Filter.eventually_cofinite]
    refine ((Set.finite_Iic (B + 2 * k.succ)).preimage Subtype.val_injective.injOn).subset ?_
    intro q hq
    simp only [Set.mem_preimage, Set.mem_Iic]
    by_contra hbig
    apply hq
    have hbig' : B + 2 * k.succ < (q : ℕ) := by omega
    have hq' : 2 * ((k.succ : ℕ) : ℝ) ≤ ((q : ℕ) : ℝ) := by
      exact_mod_cast (by omega : 2 * k.succ ≤ (q : ℕ))
    have hq1 : (1 : ℝ) ≤ ((q : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ (q : ℕ))
    rw [Real.norm_eq_abs, hf]
    dsimp only
    rw [heq _ (by omega)]
    exact factor_sub_one_le' k.succ _ hq' hq1
  have hlog : Summable fun q => Real.log (f q) :=
    (Real.summable_log_one_add_of_summable hg).congr fun q => by rw [add_sub_cancel]
  rw [← Real.rexp_tsum_eq_tprod hpos hlog]
  exact Real.exp_pos _

lemma integral_pos (k : ℕ) {n : ℝ} (hn : 3 ≤ n) :
    0 < ∫ t in (2 : ℝ)..n, 1 / t.log ^ k.succ := by
  have hI : Set.uIcc (2 : ℝ) n = Set.Icc 2 n := Set.uIcc_of_le (by linarith)
  have hpos : ∀ t ∈ Set.uIcc (2 : ℝ) n, 0 < Real.log t := by
    intro t ht
    rw [hI] at ht
    exact Real.log_pos (by linarith [ht.1])
  apply intervalIntegral.intervalIntegral_pos_of_pos_on
  · apply ContinuousOn.intervalIntegrable
    refine ContinuousOn.div continuousOn_const
      ((Real.continuousOn_log.mono fun t ht => ?_).pow k.succ) fun t ht => ?_
    · rw [hI] at ht
      exact Set.mem_compl_singleton_iff.mpr (by linarith [ht.1] : (0 : ℝ) < t).ne'
    · show Real.log t ^ k.succ ≠ 0
      exact pow_ne_zero _ (hpos t ht).ne'
  · intro t ht
    have : 0 < Real.log t := Real.log_pos (by linarith [ht.1])
    positivity
  · linarith

/-- If the first Hardy–Littlewood conjecture holds for `t` and its constant is positive, some
`p` makes every `p + tᵢ` prime. -/
lemma exists_constellation_of {k : ℕ} (t : Fin k.succ → ℕ) (B : ℕ)
    (h0 : t 0 = 0) (hev : ∀ i ≠ 0, Even (t i)) (hinj : Function.Injective t)
    (hlt : ∀ q : ℕ, q.Prime → Nat.numResidues q t < q)
    (heq : ∀ q : ℕ, B < q → Nat.numResidues q t = k.succ)
    (hHL : FirstHardyLittlewoodConjectureFor t) :
    ∃ p, ∀ i, (p + t i).Prime := by
  classical
  have h := hHL h0 hev hinj
  dsimp only at h
  have hC := tprod_pos t B hlt heq
  have hv : ∀ᶠ n : ℕ in atTop,
      (2 ^ k * ∏' (q : { q : ℕ // q.Prime ∧ 3 ≤ q}),
        (1 - (Nat.numResidues q t : ℝ) / q) / (1 - 1 / q) ^ k.succ) *
        (∫ x in (2 : ℝ)..n, 1 / x.log ^ k.succ) ≠ 0 := by
    filter_upwards [eventually_ge_atTop 3] with n hn
    exact (mul_pos (mul_pos (by positivity) hC)
      (integral_pos k (by exact_mod_cast hn))).ne'
  obtain ⟨n, hn1, hn2⟩ := (hv.and h.isBigO_symm.eq_zero_imp).exists
  have hcount : Nat.primeTupleCounting t n ≠ 0 := by
    intro h0; exact hn1 (hn2 (by simp [h0]))
  unfold Nat.primeTupleCounting at hcount
  rw [Nat.count_eq_card_filter_range, Finset.card_ne_zero] at hcount
  obtain ⟨p, hp⟩ := hcount
  exact ⟨p, (Finset.mem_filter.mp hp).2.1.2.2⟩

/-- Under the first Hardy–Littlewood conjecture, some `p` makes every `p + mᵢ` prime. -/
lemma exists_constellation
    (hHL : ∀ {k : ℕ} (m : Fin k.succ → ℕ), FirstHardyLittlewoodConjectureFor m) :
    ∃ p, ∀ i, (p + m i).Prime :=
  exists_constellation_of m 3158 m_zero (fun i _ => m_even i) m_injective numResidues_lt
    numResidues_eq (hHL (k := 446) m)

end HardyLittlewood.Richards

namespace HardyLittlewood

-- `hx`, `hy` are unused binder names of the copied statement.
set_option linter.unusedVariables false in
open Richards in
/-- Richards [Ri74] showed that only one of the two Hardy-Littlewood conjectures can be true.

[Ri74] Richards, Ian (1974). _On the Incompatibility of Two Conjectures Concerning Primes_. Bull. Amer. Math. Soc. 80: 419–438.
-/
theorem not_first_and_secondHardyLittlewoodConjecture :
    (∀ {k : ℕ} (m : Fin k.succ → ℕ), FirstHardyLittlewoodConjectureFor m) →
      ¬(∀ {x y : ℕ} (hx : 2 ≤ x) (hy : 2 ≤ y), SecondHardyLittlewoodConjectureFor x y) := by
  intro hHL hHL2
  obtain ⟨p, hp⟩ := exists_constellation hHL
  -- `p` is odd: `p` and `p + 2` are both prime.
  have hp3 : 3 ≤ p := by
    have h0 := hp 0
    have h1 := hp 1
    rw [m_zero] at h0
    rw [m_one] at h1
    have h2 := h0.two_le
    by_contra hlt
    have : p = 2 := by omega
    subst this
    exact absurd h1 (by norm_num)
  have h2 := hHL2 (x := p - 1) (y := 3159) (by omega) (by norm_num)
  unfold SecondHardyLittlewoodConjectureFor at h2
  have h3 := primeCounting_3159_le
  generalize π 3159 = c at h2 h3
  unfold Nat.primeCounting Nat.primeCounting' at h2
  have e1 : p - 1 + 3159 + 1 = p + 3159 := by omega
  have e2 : p - 1 + 1 = p := by omega
  rw [e1, e2, Nat.count_add] at h2
  -- the 447 entries of the tuple give 447 primes `p + x` with `x < 3159`
  have hcard : 447 ≤ Nat.count (fun k => (p + k).Prime) 3159 := by
    rw [Nat.count_eq_card_filter_range]
    calc 447 = tuple.toFinset.card := by
            rw [List.toFinset_card_of_nodup tuple_nodup, tuple_length]
      _ ≤ _ := by
        apply Finset.card_le_card
        intro x hx
        rw [List.mem_toFinset] at hx
        obtain ⟨i, rfl⟩ := (mem_tuple_iff x).mp hx
        rw [Finset.mem_filter, Finset.mem_range]
        exact ⟨by have := m_le i; omega, hp i⟩
  omega

end HardyLittlewood
