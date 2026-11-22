import Grosswald.Analytic
import Grosswald.Crit
import Grosswald.Combi
import Erdos985.Compute.Checker

/-!
# Algorithm 1 of MTT as a verified checker

A node `(n, X, Y)` stands for the primes `p > 2.5·10^15` with `ω(p - 1) = n`, every `q ∈ X`
dividing `p - 1` and no `q ∈ Y` dividing `p - 1`. For such `p`:

* *lower bound*: `p ≥ 1 + ∏ L`, `L` = the first `n` primes outside `Y` (`Combi`);
* *upper bound*: for `M` = the `s` largest elements of `L`, `δ = 1 - Σ_M 1/q > 0` and
  `crit (2^{n-s}(2 + (s-1)/δ) - 1) Y0`, every `p ≥ (Y0² + 2)²` satisfies a sieve inequality,
  so (under GRH) it has a small prime primitive root;
* if the interval is empty we are done; if it holds many `p ≡ 1 (mod ∏X)` we split on the next
  prime `q` (`q ∣ p - 1` or not); otherwise every `p = k ∏X + 1` in the interval is checked:
  some `q ∈ Y` divides `k`, or `p` has a small odd prime factor, or the base-2 Fermat test fails,
  or `ω(p - 1) ≠ n`, or a prime `q < ⌊√p⌋ - 2` passes Lucas' test, or `minFac p ≠ p`.

Only `checkNode_sound` matters for correctness; heuristics (`bestUpper`, `nextPrime`, the
binary search) are re-verified or irrelevant.
-/

namespace Grosswald.Alg

open Erdos985.Compute (powMod smallPrimes)

/-- `2.5·10^15 + 1`. -/
def LOW : ℕ := 2500000000000001

/-- Split while more than this many `k` remain. -/
def LIM : ℕ := 1000000

/-- The primes below `2000`. -/
def primesList : List ℕ := (List.range 2000).filter (fun q => Nat.Prime q)

/-- The first `n` primes not in `Y`. -/
def firstPrimesAvoiding (n : ℕ) (Y : List ℕ) : List ℕ :=
  (primesList.filter (fun q => q ∉ Y)).take n

/-- Validity of `L` as "the first `n` primes outside `Y`" (only downward closure matters). -/
def LOk (n : ℕ) (Y L : List ℕ) : Bool :=
  decide (L.length = n) && decide L.Nodup && L.all (fun l => decide (Nat.Prime l) && decide (l ∉ Y)) &&
    (List.range (L.foldr max 0 + 1)).all (fun q => !(decide (Nat.Prime q)) || decide (q ∈ Y) || decide (q ∈ L))

/-- `δ = 1 - Σ_{q ∈ M} 1/q`. -/
def δQ (M : List ℕ) : ℚ := 1 - (M.map (fun q : ℕ => (1 : ℚ) / (q : ℚ))).sum

/-- The sieve constant `2^{n-s} (2 + (s-1)/δ) - 1`. -/
def KQ (n s : ℕ) (δ : ℚ) : ℚ := 2 ^ (n - s) * (2 + ((s : ℚ) - 1) / δ) - 1

/-- Binary search for a small `Y0` with `crit K Y0` (heuristic). -/
def bsearch (K : ℚ) : ℕ → ℕ → ℕ → ℕ
  | 0, _, hi => hi
  | f + 1, lo, hi =>
    if hi ≤ lo + 1 then hi
    else
      let mid := (lo + hi) / 2
      if Crit.crit K mid then bsearch K f lo mid else bsearch K f mid hi

def findY0 (K : ℚ) : Option ℕ :=
  if Crit.crit K (2 ^ 40) then some (bsearch K 64 0 (2 ^ 40)) else none

/-- The upper-bound certificate check for `(s, Y0)`. -/
def upperOk (n : ℕ) (L : List ℕ) (s Y0 : ℕ) : Bool :=
  decide (s ≤ n) && decide (0 < δQ (L.drop (n - s))) &&
    Crit.crit (KQ n s (δQ (L.drop (n - s)))) Y0

/-- Best `(s, Y0)` (heuristic: minimises `Y0`). -/
def bestUpper (n : ℕ) (L : List ℕ) : Option (ℕ × ℕ) :=
  (List.range n).foldl (fun acc s =>
    let δ := δQ (L.drop (n - s))
    if 0 < δ then
      match findY0 (KQ n s δ) with
      | none => acc
      | some Y0 =>
        match acc with
        | none => some (s, Y0)
        | some (_, Y1) => if Y0 < Y1 then some (s, Y0) else acc
    else acc) none

/-- Lower and upper end of a node's interval, if its certificates check. -/
def nodeBase (n : ℕ) (Y : List ℕ) : Option (ℕ × ℕ) :=
  let L := firstPrimesAvoiding n Y
  match bestUpper n L with
  | none => none
  | some (s, Y0) =>
    if LOk n Y L && upperOk n L s Y0 then some (max (L.prod + 1) LOW, (Y0 ^ 2 + 2) ^ 2) else none

/-- Odd primes used for a cheap compositeness test. -/
def smallOdd : List ℕ := [3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71,
  73, 79, 83, 89, 97]

/-- A prime `q < ⌊√p⌋ - 2` passing Lucas' test against the factor list `fs`. -/
def hasRoot (p : ℕ) (fs : List ℕ) : Bool :=
  smallPrimes.any fun q => decide (q < Nat.sqrt p - 2) && fs.all fun r => powMod q ((p - 1) / r) p != 1

/-- The check of one candidate `p = k ∏X + 1`. -/
def candOk (n : ℕ) (X Y : List ℕ) (prodX k : ℕ) : Bool :=
  let p := k * prodX + 1
  Y.any (fun q => k % q == 0) || smallOdd.any (fun q => p % q == 0) ||
    powMod 2 (p - 1) p != 1 ||
    (let fs := (X ++ k.primeFactorsList).dedup
     fs.length != n || hasRoot p fs) ||
    p.minFac != p

/-- `f lo && … && f (lo + c - 1)`. -/
def checkRange (f : ℕ → Bool) : ℕ → ℕ → Bool
  | _, 0 => true
  | lo, c + 1 => f lo && checkRange f (lo + 1) c

/-- Enumerate a leaf. -/
def enumOk (n : ℕ) (X Y : List ℕ) (lo up : ℕ) : Bool :=
  let prodX := X.prod
  let k0 := (lo - 1) / prodX
  let k1 := (up - 1) / prodX
  decide X.Nodup && X.all (fun q => decide (Nat.Prime q)) &&
    checkRange (candOk n X Y prodX) k0 (k1 + 1 - k0)

/-- The next prime not in `X ∪ Y` (heuristic). -/
def nextPrime (X Y : List ℕ) : ℕ := (primesList.find? (fun q => q ∉ X && q ∉ Y)).getD 2

/-- Algorithm 1. -/
def checkNode (n : ℕ) : ℕ → List ℕ → List ℕ → Bool
  | 0, X, Y =>
    match nodeBase n Y with
    | none => false
    | some (lo, up) => decide (up ≤ lo) || enumOk n X Y lo up
  | f + 1, X, Y =>
    match nodeBase n Y with
    | none => false
    | some (lo, up) =>
      decide (up ≤ lo) ||
        if LIM < (up - lo) / X.prod then
          checkNode n f (nextPrime X Y :: X) Y && checkNode n f X (nextPrime X Y :: Y)
        else enumOk n X Y lo up

/-! ### Soundness -/

/-- The primes covered by a node. -/
def InClass (n : ℕ) (X Y : List ℕ) (p : ℕ) : Prop :=
  p.Prime ∧ 2500000000000000 < p ∧ (p - 1).primeFactors.card = n ∧ (∀ q ∈ X, q ∣ p - 1) ∧
    ∀ q ∈ Y, ¬ q ∣ p - 1

/-- `p` violates every admissible sieve inequality (what GRH gives when `p` is a
counterexample). -/
def NoSieve (p : ℕ) : Prop :=
  ∀ S ⊆ (p - 1).primeFactors, 0 < deltaOf S →
    ¬ SieveIneq (p - 1).primeFactors.card S.card (deltaOf S) p

lemma le_foldr_max {l : ℕ} : ∀ {L : List ℕ}, l ∈ L → l ≤ L.foldr max 0
  | a :: L, h => by
    rcases List.mem_cons.mp h with rfl | h
    · exact le_max_left _ _
    · exact (le_foldr_max h).trans (le_max_right _ _)

lemma LOk_spec {n : ℕ} {Y L : List ℕ} (h : LOk n Y L = true) :
    L.length = n ∧ L.Nodup ∧ (∀ l ∈ L, l.Prime ∧ l ∉ Y) ∧
      ∀ q, q.Prime → q ∉ Y → q ∉ L → ∀ l ∈ L, l < q := by
  simp only [LOk, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, Bool.or_eq_true,
    Bool.not_eq_true', decide_eq_false_iff_not, List.mem_range] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  refine ⟨h1, h2, h3, fun q hq hqY hqL l hl => ?_⟩
  by_contra hlt
  have hle := le_foldr_max hl
  rcases h4 q (by omega) with (h | h) | h
  · exact h hq
  · exact hqY h
  · exact hqL h

lemma two_le_of_inClass {n : ℕ} {X Y : List ℕ} {p : ℕ} (hp : InClass n X Y p) : 2 ≤ p - 1 := by
  have := hp.2.1; omega

lemma dominates {n : ℕ} {X Y L : List ℕ} {p : ℕ} (hL : LOk n Y L = true) (hp : InClass n X Y p) :
    ∀ q ∈ (p - 1).primeFactors, q ∉ L.toFinset → ∀ l ∈ L.toFinset, l < q := by
  intro q hq hqL l hl
  obtain ⟨-, -, -, h4⟩ := LOk_spec hL
  have hq' := Nat.mem_primeFactors.mp hq
  refine h4 q hq'.1 (fun hY => hp.2.2.2.2 q hY hq'.2.1) (by simpa using hqL) l (by simpa using hl)

/-- The lower bound `p ≥ 1 + ∏ L`. -/
lemma lower_le {n : ℕ} {X Y L : List ℕ} {p : ℕ} (hL : LOk n Y L = true) (hp : InClass n X Y p) :
    L.prod + 1 ≤ p := by
  obtain ⟨h1, h2, -, -⟩ := LOk_spec hL
  have hc : (p - 1).primeFactors.card = L.toFinset.card := by
    rw [hp.2.2.1, List.toFinset_card_of_nodup h2, h1]
  have hprod := Combi.prod_le_prod_of_dominates hc (dominates hL hp)
  rw [List.prod_toFinset _ h2, List.map_id'] at hprod
  have := two_le_of_inClass hp
  have hdvd : ∏ q ∈ (p - 1).primeFactors, q ≤ p - 1 :=
    Nat.le_of_dvd (by have := two_le_of_inClass hp; omega) (Nat.prod_primeFactors_dvd _)
  omega

lemma cast_sum_inv : ∀ l : List ℕ,
    (((l.map (fun q : ℕ => (1 : ℚ) / (q : ℚ))).sum : ℚ) : ℝ) = (l.map (fun q : ℕ => 1 / (q : ℝ))).sum
  | [] => by simp
  | a :: l => by
    rw [List.map_cons, List.map_cons, List.sum_cons, List.sum_cons, Rat.cast_add, cast_sum_inv l]
    push_cast; rfl

lemma δQ_eq {l : List ℕ} (hl : l.Nodup) : (δQ l : ℝ) = 1 - ∑ q ∈ l.toFinset, 1 / (q : ℝ) := by
  rw [List.sum_toFinset _ hl, δQ, Rat.cast_sub, Rat.cast_one, cast_sum_inv]

lemma bachC_nonneg (p x : ℕ) (hp : 1 < p) (hx : 1 ≤ x) : 0 ≤ Erdos985.bachC p x := by
  have hl : 0 < Real.log p := Real.log_pos (by exact_mod_cast hp)
  have hlx : 0 ≤ Real.log x := Real.log_nonneg (by exact_mod_cast hx)
  unfold Erdos985.bachC
  have : 0 ≤ (Real.log x + 2) / (√(x : ℝ) * Real.log p) := by positivity
  positivity

/-- The upper bound: a valid certificate `(s, Y0)` excludes every `p ≥ (Y0² + 2)²`. -/
lemma lt_upper {n s Y0 : ℕ} {X Y L : List ℕ} {p : ℕ} (hL : LOk n Y L = true)
    (hu : upperOk n L s Y0 = true) (hp : InClass n X Y p) (hns : NoSieve p) :
    p < (Y0 ^ 2 + 2) ^ 2 := by
  simp only [upperOk, Bool.and_eq_true, decide_eq_true_eq] at hu
  obtain ⟨⟨hsn, hδ⟩, hcrit⟩ := hu
  obtain ⟨h1, h2, h3, -⟩ := LOk_spec hL
  by_contra hge
  rw [not_lt] at hge
  set F := (p - 1).primeFactors with hF
  set L₀ := (L.take (n - s)).toFinset with hL₀
  set M := (L.drop (n - s)).toFinset with hM
  have hMnd : (L.drop (n - s)).Nodup := h2.sublist (List.drop_sublist _ _)
  have hMc : M.card = s := by
    rw [hM, List.toFinset_card_of_nodup hMnd, List.length_drop, h1]; omega
  have hL₀c : L₀.card ≤ n - s := by
    refine (List.toFinset_card_le _).trans ?_
    rw [List.length_take]; omega
  have hFc : F.card = n := hp.2.2.1
  have hsd : s ≤ (F \ L₀).card := by
    have := Finset.le_card_sdiff L₀ F; omega
  obtain ⟨S, hSsub, hSc⟩ := Finset.exists_subset_card_eq hsd
  have hSF : S ⊆ F := hSsub.trans Finset.sdiff_subset
  have hML : M ⊆ L.toFinset := by
    intro q hq
    rw [hM, List.mem_toFinset] at hq
    exact List.mem_toFinset.mpr (List.mem_of_mem_drop hq)
  have hdomS : ∀ q ∈ S, q ∉ M → ∀ l ∈ L.toFinset, l < q := by
    intro q hq hqM
    have hq' := Finset.mem_sdiff.mp (hSsub hq)
    apply dominates hL hp q hq'.1
    intro hqL
    rw [List.mem_toFinset, ← List.take_append_drop (n - s) L, List.mem_append] at hqL
    rcases hqL with h | h
    · exact hq'.2 (List.mem_toFinset.mpr h)
    · exact hqM (List.mem_toFinset.mpr h)
  have hpos : ∀ l ∈ L.toFinset, 0 < l := fun l hl => (h3 l (List.mem_toFinset.mp hl)).1.pos
  have hsum := Combi.sum_inv_le_of_dominates hML (hSc.trans hMc.symm) hpos hdomS
  have hδM := δQ_eq hMnd
  rw [← hM] at hδM
  have hδMpos : (0 : ℝ) < δQ (L.drop (n - s)) := by exact_mod_cast hδ
  have hδS : (δQ (L.drop (n - s)) : ℝ) ≤ deltaOf S := by
    rw [hδM, deltaOf]; linarith
  have hδSpos : 0 < deltaOf S := lt_of_lt_of_le hδMpos hδS
  apply hns S hSF hδSpos
  rw [hFc, hSc]
  -- the sieve inequality for `S`
  have hc := Crit.crit_sound hcrit p hge
  unfold SieveIneq xOf
  have hx1 : 1 ≤ Nat.sqrt p - 2 := by
    have : 3 ≤ Nat.sqrt p := Nat.le_sqrt.mpr (by have := hp.2.1; omega)
    omega
  have hA : 0 ≤ Erdos985.bachC p (Nat.sqrt p - 2 : ℕ) * √((Nat.sqrt p - 2 : ℕ) : ℝ) * Real.log p := by
    have := bachC_nonneg p (Nat.sqrt p - 2) (by have := hp.2.1; omega) hx1
    have : 0 ≤ Real.log p := Real.log_nonneg (by exact_mod_cast (by have := hp.2.1; omega : 1 ≤ p))
    positivity
  have hK : sieveK n s (deltaOf S) ≤ (KQ n s (δQ (L.drop (n - s))) : ℝ) := by
    unfold sieveK KQ
    push_cast
    have h2p : (0 : ℝ) < 2 ^ (n - s) := by positivity
    rcases Nat.eq_zero_or_pos s with hs0 | hs0
    · subst hs0
      have hS0 : S = ∅ := Finset.card_eq_zero.mp hSc
      have hM0 : M = ∅ := Finset.card_eq_zero.mp hMc
      have e1 : deltaOf S = 1 := by simp [deltaOf, hS0]
      have e2 : (δQ (L.drop (n - 0)) : ℝ) = 1 := by rw [hδM, hM0]; simp
      rw [e1, e2]
    · have hs1 : (0 : ℝ) ≤ (s : ℝ) - 1 := by
        have : (1 : ℝ) ≤ s := by exact_mod_cast hs0
        linarith
      have : ((s : ℝ) - 1) / deltaOf S ≤ ((s : ℝ) - 1) / (δQ (L.drop (n - s)) : ℝ) :=
        div_le_div_of_nonneg_left hs1 hδMpos hδS
      nlinarith
  calc sieveK n s (deltaOf S) * (Erdos985.bachC p (Nat.sqrt p - 2 : ℕ)
        * √((Nat.sqrt p - 2 : ℕ) : ℝ) * Real.log p)
      ≤ (KQ n s (δQ (L.drop (n - s))) : ℝ) * (Erdos985.bachC p (Nat.sqrt p - 2 : ℕ)
        * √((Nat.sqrt p - 2 : ℕ) : ℝ) * Real.log p) := mul_le_mul_of_nonneg_right hK hA
    _ < _ := hc

lemma nodeBase_sound {n lo up : ℕ} {X Y : List ℕ} {p : ℕ} (h : nodeBase n Y = some (lo, up))
    (hp : InClass n X Y p) (hns : NoSieve p) : lo ≤ p ∧ p < up := by
  unfold nodeBase at h
  dsimp only at h
  split at h
  · exact absurd h (by simp)
  · split_ifs at h with hc
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp only [Bool.and_eq_true] at hc
    refine ⟨max_le (lower_le hc.1 hp) ?_, lt_upper hc.1 hc.2 hp hns⟩
    have := hp.2.1; unfold LOW; omega

theorem checkRange_sound (f : ℕ → Bool) : ∀ (c lo : ℕ), checkRange f lo c = true →
    ∀ k, lo ≤ k → k < lo + c → f k = true
  | 0, lo, _, k, h1, h2 => by omega
  | c + 1, lo, h, k, h1, h2 => by
    simp only [checkRange, Bool.and_eq_true] at h
    rcases Nat.eq_or_lt_of_le h1 with rfl | h1
    · exact h.1
    · exact checkRange_sound f c (lo + 1) h.2 k h1 (by omega)

lemma fermat {p q : ℕ} (hp : p.Prime) (hq0 : 0 < q) (hqp : q < p) : powMod q (p - 1) p = 1 := by
  have : Fact p.Prime := ⟨hp⟩
  rw [← Erdos985.Compute.zmod_pow_eq_one_iff hp.two_le]
  apply ZMod.pow_card_sub_one_eq_one
  intro h0
  rw [ZMod.natCast_eq_zero_iff] at h0
  have := Nat.le_of_dvd hq0 h0
  omega

lemma candOk_sound {n k : ℕ} {X Y : List ℕ} {p : ℕ} (h : candOk n X Y X.prod k = true)
    (hX : X.Nodup) (hXp : ∀ q ∈ X, q.Prime) (hp : InClass n X Y p) (hpk : p = k * X.prod + 1) :
    HasSmallPrimePrimitiveRoot p := by
  obtain ⟨hpr, hbig, hn, hXd, hY⟩ := hp
  have hXprod : X.prod = ∏ q ∈ X.toFinset, q := by rw [List.prod_toFinset _ hX, List.map_id']
  have hX0 : 0 < X.prod := by
    rw [hXprod]; exact Finset.prod_pos fun q hq => (hXp q (List.mem_toFinset.mp hq)).pos
  have hpm1 : p - 1 = X.prod * k := by rw [hpk, Nat.add_sub_cancel, mul_comm]
  have hk0 : k ≠ 0 := by rintro rfl; simp at hpk; omega
  have h2p : 2 ≤ p := hpr.two_le
  simp only [candOk, Bool.or_eq_true, List.any_eq_true, beq_iff_eq, bne_iff_ne, ne_eq,
    ← hpk] at h
  rcases h with ((((⟨q, hqY, hq⟩ | ⟨q, hq, hq'⟩) | hF) | hfs) | hmin)
  · exact absurd (hpm1 ▸ Dvd.dvd.mul_left (Nat.dvd_of_mod_eq_zero hq) _) (hY q hqY)
  · have hqp : q ∣ p := Nat.dvd_of_mod_eq_zero hq'
    have h397 : 3 ≤ q ∧ q ≤ 97 := by
      simp only [smallOdd, List.mem_cons, List.not_mem_nil, or_false] at hq; omega
    rcases hpr.eq_one_or_self_of_dvd q hqp with h | h <;> omega
  · exact absurd (fermat hpr two_pos (by omega)) hF
  · set fs := (X ++ k.primeFactorsList).dedup with hfsdef
    have hfsF : fs.toFinset = (p - 1).primeFactors := by
      rw [hfsdef, List.toFinset_dedup, List.toFinset_append, hpm1,
        Nat.primeFactors_mul hX0.ne' hk0, hXprod,
        Nat.primeFactors_prod (fun q hq => hXp q (List.mem_toFinset.mp hq))]
      rfl
    have hlen : fs.length = n := by
      rw [← List.toFinset_card_of_nodup (List.nodup_dedup _), hfsF, hn]
    rcases hfs with hl | hr
    · exact absurd hlen hl
    · simp only [hasRoot, List.any_eq_true, Bool.and_eq_true, decide_eq_true_eq,
        List.all_eq_true, bne_iff_ne, ne_eq] at hr
      obtain ⟨q, hq, hqx, hall⟩ := hr
      have hqp := Erdos985.Compute.prime_of_mem_smallPrimes hq
      have hqlt : q < p := by have := Nat.sqrt_le_self p; omega
      refine ⟨q, hqp, lt_sqrt_sub_two_of_lt_xOf hqx, ?_⟩
      apply orderOf_eq_of_pow_and_pow_div_prime
      · exact (Erdos985.Compute.zmod_pow_eq_one_iff h2p _ _).mpr (fermat hpr hqp.pos hqlt)
      · intro r hr hrd
        rw [ne_eq, Erdos985.Compute.zmod_pow_eq_one_iff h2p]
        apply hall r
        rw [← List.mem_toFinset, hfsF]
        exact Nat.mem_primeFactors.mpr ⟨hr, hrd, by omega⟩
  · exact absurd (Nat.prime_def_minFac.mp hpr).2 hmin

lemma enumOk_sound {n lo up : ℕ} {X Y : List ℕ} {p : ℕ} (h : enumOk n X Y lo up = true)
    (hp : InClass n X Y p) (hlo : lo ≤ p) (hup : p < up) : HasSmallPrimePrimitiveRoot p := by
  simp only [enumOk, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
  obtain ⟨⟨hX, hXp⟩, hr⟩ := h
  have hXprod : X.prod = ∏ q ∈ X.toFinset, q := by rw [List.prod_toFinset _ hX, List.map_id']
  have hX0 : 0 < X.prod := by
    rw [hXprod]; exact Finset.prod_pos fun q hq => (hXp q (List.mem_toFinset.mp hq)).pos
  have hdvd : X.prod ∣ p - 1 := by
    rw [hXprod]
    exact Finset.prod_primes_dvd _ (fun q hq => (hXp q (List.mem_toFinset.mp hq)).prime)
      (fun q hq => hp.2.2.2.1 q (List.mem_toFinset.mp hq))
  obtain ⟨k, hk⟩ := hdvd
  have h2 := two_le_of_inClass hp
  have hpk : p = k * X.prod + 1 := by rw [mul_comm]; omega
  apply candOk_sound _ hX hXp hp hpk
  have hk' : (p - 1) / X.prod = k := by rw [hk, Nat.mul_div_cancel_left _ hX0]
  have e1 : (lo - 1) / X.prod ≤ k := hk' ▸ Nat.div_le_div_right (by omega)
  have e2 : k ≤ (up - 1) / X.prod := hk' ▸ Nat.div_le_div_right (by omega)
  exact checkRange_sound _ _ _ hr k e1 (by omega)

/-- **Soundness of Algorithm 1.** -/
theorem checkNode_sound (n : ℕ) : ∀ (fuel : ℕ) (X Y : List ℕ), checkNode n fuel X Y = true →
    ∀ p, InClass n X Y p → NoSieve p → HasSmallPrimePrimitiveRoot p := by
  intro fuel
  induction fuel with
  | zero =>
    intro X Y h p hp hns
    unfold checkNode at h
    cases hb : nodeBase n Y with
    | none => rw [hb] at h; exact absurd h (by simp)
    | some lu =>
      obtain ⟨lo, up⟩ := lu
      rw [hb] at h
      dsimp only at h
      obtain ⟨hlo, hup⟩ := nodeBase_sound hb hp hns
      simp only [Bool.or_eq_true, decide_eq_true_eq] at h
      rcases h with h | h
      · omega
      · exact enumOk_sound h hp hlo hup
  | succ f ih =>
    intro X Y h p hp hns
    unfold checkNode at h
    cases hb : nodeBase n Y with
    | none => rw [hb] at h; exact absurd h (by simp)
    | some lu =>
      obtain ⟨lo, up⟩ := lu
      rw [hb] at h
      dsimp only at h
      obtain ⟨hlo, hup⟩ := nodeBase_sound hb hp hns
      simp only [Bool.or_eq_true, decide_eq_true_eq] at h
      rcases h with h | h
      · omega
      · split_ifs at h with hlim
        · simp only [Bool.and_eq_true] at h
          obtain ⟨hpr, hbig, hn, hX, hY⟩ := hp
          by_cases hq : nextPrime X Y ∣ p - 1
          · refine ih _ _ h.1 p ⟨hpr, hbig, hn, fun r hr => ?_, hY⟩ hns
            rcases List.mem_cons.mp hr with h' | hr
            · rw [h']; exact hq
            · exact hX r hr
          · refine ih _ _ h.2 p ⟨hpr, hbig, hn, hX, fun r hr => ?_⟩ hns
            rcases List.mem_cons.mp hr with h' | hr
            · rw [h']; exact hq
            · exact hY r hr
        · exact enumOk_sound h hp hlo hup

end Grosswald.Alg
