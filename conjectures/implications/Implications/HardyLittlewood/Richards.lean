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
    exact ⟨Fin.cast tuple_length j, rfl⟩
  · rintro ⟨i, rfl⟩
    exact ⟨_, rfl⟩

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
    List.all_eq_true, bne_iff_ne, ne_eq] at h
  have hq' : 2 + (q - 2) = q := by omega
  rw [hq'] at h
  refine ⟨_, h.1, fun i => h.2 _ (m_mem i)⟩

/-- The number of classes mod `q` met by the tuple is below `q`, for every prime `q`. -/
lemma numResidues_lt (q : ℕ) (hq : q.Prime) : Nat.numResidues q m < q := by
  haveI : NeZero q := ⟨hq.ne_zero⟩
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

/-- The elementary estimate behind the convergence of the singular series. -/
lemma factor_sub_one_le (q : ℝ) (hq : 894 ≤ q) :
    |(1 - 447 / q) / (1 - 1 / q) ^ 447 - 1| ≤ 2 * 447 ^ 2 * (1 / q ^ 2) := by
  have hq0 : 0 < q := by linarith
  set x : ℝ := 1 / q with hxdef
  have hx0 : 0 < x := by positivity
  have hx1 : 447 * x ≤ 1 / 2 := by
    rw [hxdef, mul_one_div, div_le_iff₀ hq0]; linarith
  have h447 : (447 : ℝ) / q = 447 * x := by rw [hxdef, mul_one_div]
  have hx2 : 1 / q ^ 2 = x ^ 2 := by rw [hxdef, one_div_pow]
  rw [h447, hx2]
  set P : ℝ := (1 - x) ^ 447 with hP
  have hlow : 1 - 447 * x ≤ P := by
    have := one_add_mul_le_pow (a := -x) (by linarith) 447
    rw [hP]; norm_num at this ⊢; linarith
  have hup : P ≤ 1 - 447 * x + (447 * x) ^ 2 := by
    have h1 : P ≤ Real.exp (-x) ^ 447 :=
      pow_le_pow_left₀ (by linarith) (Real.one_sub_le_exp_neg x) 447
    have h2 : Real.exp (-x) ^ 447 = Real.exp (-(447 * x)) := by
      rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
    have h3 := Real.abs_exp_sub_one_sub_id_le (x := -(447 * x))
      (by rw [abs_neg, abs_of_pos (by positivity)]; linarith)
    have h4 := (abs_le.mp h3).2
    rw [neg_sq] at h4
    linarith
  have hPpos : 1 / 2 ≤ P := by linarith
  have hP0 : 0 < P := by linarith
  rw [div_sub_one hP0.ne', abs_div, abs_of_pos hP0, div_le_iff₀ hP0,
    abs_of_nonpos (by linarith)]
  nlinarith [sq_nonneg x]

/-- The Hardy–Littlewood factor at `q` for our tuple. -/
noncomputable def factor (q : { q : ℕ // q.Prime ∧ 3 ≤ q}) : ℝ :=
  (1 - (Nat.numResidues q m : ℝ) / q) / (1 - 1 / q) ^ (Nat.succ 446)

lemma factor_pos (q : { q : ℕ // q.Prime ∧ 3 ≤ q}) : 0 < factor q := by
  have hq3 : (3 : ℝ) ≤ (q : ℕ) := by exact_mod_cast q.2.2
  have hlt : (Nat.numResidues q m : ℝ) < (q : ℕ) := by exact_mod_cast numResidues_lt q q.2.1
  unfold factor
  apply div_pos
  · rw [sub_pos, div_lt_one (by linarith)]; exact hlt
  · apply pow_pos
    rw [sub_pos, div_lt_one (by linarith)]; linarith

lemma summable_log_factor : Summable fun q => Real.log (factor q) := by
  have hg : Summable fun q : { q : ℕ // q.Prime ∧ 3 ≤ q} => factor q - 1 := by
    have hs : Summable fun q : { q : ℕ // q.Prime ∧ 3 ≤ q} =>
        2 * 447 ^ 2 * (1 / ((q : ℕ) : ℝ) ^ 2) :=
      ((Real.summable_one_div_nat_pow.mpr one_lt_two).comp_injective
        Subtype.val_injective).mul_left _
    refine hs.of_norm_bounded_eventually ?_
    rw [Filter.eventually_cofinite]
    refine ((Set.finite_Iic 3158).preimage Subtype.val_injective.injOn).subset ?_
    intro q hq
    simp only [Set.mem_setOf_eq, Set.mem_preimage, Set.mem_Iic] at hq ⊢
    by_contra hbig
    apply hq
    push_neg at hbig
    have hq' : (894 : ℝ) ≤ (q : ℕ) := by exact_mod_cast (by omega : 894 ≤ (q : ℕ))
    have := factor_sub_one_le _ hq'
    rw [Real.norm_eq_abs]
    unfold factor
    rw [numResidues_eq _ hbig]
    exact_mod_cast this
  exact (Real.summable_log_one_add_of_summable hg).congr fun q => by rw [add_sub_cancel]

/-- The Hardy–Littlewood singular series of the tuple is positive. -/
lemma tprod_factor_pos : 0 < ∏' q, factor q := by
  rw [← Real.rexp_tsum_eq_tprod factor_pos summable_log_factor]
  exact Real.exp_pos _

lemma integral_pos {n : ℝ} (hn : 3 ≤ n) :
    0 < ∫ t in (2 : ℝ)..n, 1 / t.log ^ (Nat.succ 446) := by
  have hpos : ∀ t ∈ Set.uIcc (2 : ℝ) n, 0 < Real.log t := by
    intro t ht
    rw [Set.uIcc_of_le (by linarith)] at ht
    exact Real.log_pos (by linarith [ht.1])
  apply intervalIntegral.intervalIntegral_pos_of_pos_on
  · apply ContinuousOn.intervalIntegrable
    apply continuousOn_const.div
    · apply ContinuousOn.pow
      exact Real.continuousOn_log.mono fun t ht => by
        simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
        exact (Real.log_pos_iff' (by linarith [(hpos t ht)])).ne' |>.elim (fun h => h) |> fun _ =>
          ne_of_gt (lt_of_lt_of_le (by norm_num) (by
            rw [Set.uIcc_of_le (by linarith)] at ht; exact ht.1))
    · intro t ht; exact pow_ne_zero _ (hpos t ht).ne'
  · intro t ht
    have : 0 < Real.log t := Real.log_pos (by linarith [ht.1])
    positivity
  · linarith

/-- Under the first Hardy–Littlewood conjecture, some `p` makes every `p + mᵢ` prime. -/
lemma exists_constellation
    (hHL : ∀ {k : ℕ} (m : Fin k.succ → ℕ), FirstHardyLittlewoodConjectureFor m) :
    ∃ p, ∀ i, (p + m i).Prime := by
  have h := hHL (k := 446) m m_zero (fun i _ => m_even i) m_injective
  dsimp only at h
  have hC : 0 < (2 : ℝ) ^ 446 * ∏' q, factor q := by
    have := tprod_factor_pos; positivity
  have hv : ∀ᶠ n : ℕ in atTop,
      (2 ^ 446 * ∏' (q : { q : ℕ // q.Prime ∧ 3 ≤ q}),
        (1 - (Nat.numResidues q m : ℝ) / q) / (1 - 1 / q) ^ (Nat.succ 446)) *
        (∫ t in (2 : ℝ)..n, 1 / t.log ^ (Nat.succ 446)) ≠ 0 := by
    filter_upwards [eventually_ge_atTop 3] with n hn
    exact (mul_pos hC (integral_pos (by exact_mod_cast hn))).ne'
  obtain ⟨n, hn1, hn2⟩ := (hv.and h.isBigO_symm.eq_zero_imp).exists
  have hcount : Nat.primeTupleCounting m n ≠ 0 := by
    intro h0; exact hn1 (hn2 (by simp [h0]))
  unfold Nat.primeTupleCounting at hcount
  rw [Nat.count_eq_card_filter_range, Finset.card_ne_zero] at hcount
  obtain ⟨p, hp⟩ := hcount
  exact ⟨p, (Finset.mem_filter.mp hp).2.1.2.2⟩

lemma primeCounting_3159 : π 3159 = 446 := by decide +kernel

end HardyLittlewood.Richards

namespace HardyLittlewood

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
    exact absurd h1 (by decide)
  have h2 := hHL2 (x := p - 1) (y := 3159) (by omega) (by norm_num)
  unfold SecondHardyLittlewoodConjectureFor at h2
  rw [primeCounting_3159] at h2
  simp only [Nat.primeCounting, Nat.primeCounting'] at h2
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
