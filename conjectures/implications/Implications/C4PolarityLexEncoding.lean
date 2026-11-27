import Mathlib
import Implications.C4PolarityCnfGates
import Implications.C4PolarityThresholdEncoding

/-!
# DIMACS encoding of polarity lexicographic constraints

This module mirrors `Cnf.lex_at_least` in
`scripts/encode_c4_polarity_42_cnf.py`. Positions with the same DIMACS variable
are skipped without allocating a prefix variable, as in the Python encoder.
-/

namespace Implications.C4PolarityLexEncoding

open Implications.C4PolarityCnfGates
open Implications.C4PolarityThresholdEncoding

private def pos (v : Nat) : Int := Int.ofNat v
private def neg (v : Nat) : Int := Int.negOfNat v

@[simp] private theorem literalValue_pos (a : Nat → Bool) (v : Nat) (_hv : 0 < v) :
    literalValue a (pos v) = a v := by
  simp [literalValue, pos]

@[simp] private theorem literalValue_neg (a : Nat → Bool) (v : Nat) (hv : 0 < v) :
    literalValue a (neg v) = !a v := by
  change literalValue a (Int.negOfNat v) = !a v
  cases v with
  | zero => omega
  | succ n => simp [literalValue, Int.negOfNat]

/-- One nontrivial iteration of the Python lex loop: its guard clause followed
by the five clauses defining the next equality-prefix variable. -/
def lexStepClauses (pref x y same : Nat) : List (List Int) :=
  [[neg pref, pos x, neg y],
   [neg same, pos pref],
   [neg same, neg x, pos y],
   [neg same, pos x, neg y],
   [neg pref, pos x, pos y, pos same],
   [neg pref, neg x, neg y, pos same]]

/-- Compile the exact loop in `Cnf.lex_at_least`. `prefix` is the current
equality-prefix variable and `next` is the next unused variable number. -/
def lexClauses (pref next : Nat) : List Nat → List Nat → List (List Int)
  | x :: xs, y :: ys =>
      if x == y then lexClauses pref next xs ys
      else lexStepClauses pref x y next ++ lexClauses next (next + 1) xs ys
  | _, _ => []

/-- Fresh DIMACS IDs allocated by the lex loop, in allocation order. -/
def lexFreshIds (next : Nat) : List Nat → List Nat → List Nat
  | x :: xs, y :: ys =>
      if x == y then lexFreshIds next xs ys
      else next :: lexFreshIds (next + 1) xs ys
  | _, _ => []

/-- Scan the comparison from an initially equal prefix, recording one bit for
each non-skipped position. Each recorded bit is the updated equality prefix. -/
def lexPrefixScan (a : Nat → Bool) (pref : Bool) : List Nat → List Nat → List Bool
  | x :: xs, y :: ys =>
      if x == y then lexPrefixScan a pref xs ys
      else
        let nextPref := pref && (a x == a y)
        nextPref :: lexPrefixScan a nextPref xs ys
  | _, _ => []

theorem lexPrefixScan_length (a : Nat → Bool) (pref : Bool)
    (left right : List Nat) :
    (lexPrefixScan a pref left right).length =
      (List.zip left right).countP (fun p => p.1 != p.2) := by
  induction left generalizing right pref with
  | nil => cases right <;> rfl
  | cons x xs ih =>
      cases right with
      | nil => rfl
      | cons y ys =>
          by_cases hxy : x = y
          · simp [lexPrefixScan, hxy, ih]
          · simp [lexPrefixScan, List.zip_cons_cons, List.countP_cons, hxy, ih]

/-- The lex auxiliary assignment uses the scan values at the consecutive DIMACS
IDs beginning at `base`; IDs outside that block retain their original value. -/
def lexAssignment (a : Nat → Bool) (base : Nat) (initialPref : Bool)
    (left right : List Nat) : Nat → Bool :=
  fun n => if n < base then a n else
    if n < base + (lexPrefixScan a initialPref left right).length then
      (lexPrefixScan a initialPref left right).getD (n - base) false
    else a n

theorem lexAssignment_preserves_below_base (a : Nat → Bool) (base : Nat) (initialPref : Bool)
    (left right : List Nat) {n : Nat} (hn : n < base) :
    lexAssignment a base initialPref left right n = a n := by
  simp [lexAssignment, hn]

theorem lexAssignment_fresh_id (a : Nat → Bool) (base : Nat) (initialPref : Bool)
    (left right : List Nat) {k : Nat}
    (hk : k < (lexPrefixScan a initialPref left right).length) :
    lexAssignment a base initialPref left right (base + k) =
      (lexPrefixScan a initialPref left right).getD k false := by
  have hbelow : ¬ base + k < base := by omega
  have habove : base + k < base + (lexPrefixScan a initialPref left right).length := by omega
  simp [lexAssignment, hbelow, habove]

theorem lexPrefixScan_extendVariable (a : Nat → Bool) (base : Nat)
    (value initialPref : Bool) (left right : List Nat)
    (hleft : ∀ x ∈ left, x < base) (hright : ∀ y ∈ right, y < base) :
    lexPrefixScan (extendVariable a base value) initialPref left right =
      lexPrefixScan a initialPref left right := by
  induction left generalizing right initialPref with
  | nil => cases right <;> rfl
  | cons x xs ih =>
      cases right with
      | nil => rfl
      | cons y ys =>
          have hx : x < base := hleft x (by simp)
          have hy : y < base := hright y (by simp)
          have htailL : ∀ z ∈ xs, z < base := by
            intro z hz
            exact hleft z (by simp [hz])
          have htailR : ∀ z ∈ ys, z < base := by
            intro z hz
            exact hright z (by simp [hz])
          have hvalx : extendVariable a base value x = a x := by
            simp [extendVariable, Nat.ne_of_lt hx]
          have hvaly : extendVariable a base value y = a y := by
            simp [extendVariable, Nat.ne_of_lt hy]
          by_cases hxy : x = y
          · have htail := ih initialPref ys htailL htailR
            simp [lexPrefixScan, hxy, hvalx, hvaly, htail]
          · have htail := ih (initialPref && (a x == a y)) ys htailL htailR
            simp [lexPrefixScan, hxy, hvalx, hvaly, htail]

theorem lexAssignment_cons_neq (a : Nat → Bool) (base : Nat)
    (initialPref : Bool) (x y : Nat) (xs ys : List Nat)
    (hxy : x ≠ y) (hx : x < base) (hy : y < base)
    (hxs : ∀ z ∈ xs, z < base) (hys : ∀ z ∈ ys, z < base) :
    lexAssignment a base initialPref (x :: xs) (y :: ys) =
      lexAssignment (extendVariable a base
        (initialPref && (a x == a y))) (base + 1)
        (initialPref && (a x == a y)) xs ys := by
  funext n
  let nextPref := initialPref && (a x == a y)
  have hscan : lexPrefixScan a initialPref (x :: xs) (y :: ys) =
      nextPref :: lexPrefixScan a nextPref xs ys := by
    simp [lexPrefixScan, hxy, nextPref]
  have hscanExt : lexPrefixScan (extendVariable a base nextPref) nextPref xs ys =
      lexPrefixScan a nextPref xs ys :=
    lexPrefixScan_extendVariable a base nextPref nextPref xs ys hxs hys
  have hlen : (lexPrefixScan a initialPref (x :: xs) (y :: ys)).length =
      1 + (lexPrefixScan a nextPref xs ys).length := by rw [hscan]; simp [Nat.add_comm]
  by_cases hbelow : n < base
  · have hbelow' : n < base + 1 := by omega
    simp [lexAssignment, hbelow, hbelow', extendVariable, Nat.ne_of_lt hbelow]
  · by_cases heq : n = base
    · subst n
      simp [lexAssignment, hbelow, hscan, nextPref, extendVariable]
    · have habove : base < n := by omega
      have hbelow' : ¬ n < base + 1 := by omega
      have hidx : n - base = (n - (base + 1)) + 1 := by omega
      have hnotLe : ¬ n ≤ base := Nat.not_le_of_gt habove
      have hlen' : (lexPrefixScan a nextPref xs ys).length + 1 =
          1 + (lexPrefixScan a nextPref xs ys).length := by omega
      have hthresholdEq : base + (1 + (lexPrefixScan a nextPref xs ys).length) =
          base + 1 + (lexPrefixScan a nextPref xs ys).length := by omega
      have hthreshold :
          (n < base + (lexPrefixScan a initialPref (x :: xs) (y :: ys)).length) ↔
          (n < (base + 1) + (lexPrefixScan a nextPref xs ys).length) := by
        rw [hlen]
        omega
      by_cases hinside : n < base + (lexPrefixScan a initialPref (x :: xs) (y :: ys)).length
      · have hinside' : n < (base + 1) + (lexPrefixScan a nextPref xs ys).length :=
          hthreshold.mp hinside
        have hscanExt' : lexPrefixScan (extendVariable a base
            (initialPref && (a x == a y))) (initialPref && (a x == a y)) xs ys =
            lexPrefixScan a nextPref xs ys := by simpa [nextPref] using hscanExt
        have htailBound : n < base + 1 + (lexPrefixScan a nextPref xs ys).length := by
          simpa [hscanExt'] using hinside'
        simp [lexAssignment, hbelow, hbelow', hnotLe, hinside, hinside', hscan,
          hscanExt', hlen', hthresholdEq, hidx, extendVariable, Nat.ne_of_gt habove]
      · have hinside' : ¬ n < (base + 1) + (lexPrefixScan a nextPref xs ys).length :=
          fun hh => hinside (hthreshold.mpr hh)
        have hscanExt' : lexPrefixScan (extendVariable a base
            (initialPref && (a x == a y))) (initialPref && (a x == a y)) xs ys =
            lexPrefixScan a nextPref xs ys := by simpa [nextPref] using hscanExt
        have htailNotBound : ¬ n < base + 1 +
            (lexPrefixScan (extendVariable a base
              (initialPref && (a x == a y))) (initialPref && (a x == a y)) xs ys).length := by
          simpa [hscanExt'] using hinside'
        simp [lexAssignment, hbelow, hbelow', hnotLe, hinside, hinside', hscan,
          hscanExt', hlen', hthresholdEq, htailNotBound, extendVariable, Nat.ne_of_gt habove]

/-- Each unequal variable pair allocates exactly one fresh prefix variable;
identical variables are skipped. -/
theorem lexFreshIds_length (next : Nat) (left right : List Nat) :
    (lexFreshIds next left right).length =
      (List.zip left right).countP (fun p => p.1 != p.2) := by
  induction left generalizing right next with
  | nil => cases right <;> rfl
  | cons x xs ih =>
      cases right with
      | nil => rfl
      | cons y ys =>
          simp only [lexFreshIds, List.zip_cons_cons, List.countP_cons]
          by_cases hxy : x = y
          · simp [hxy, ih]
          · simp [hxy, ih]

/-- The final unused variable is the starting ID plus the number of non-skipped
positions. This is the numbering convention of the Python loop. -/
def lexNext (next : Nat) : List Nat → List Nat → Nat
  | x :: xs, y :: ys =>
      if x == y then lexNext next xs ys else lexNext (next + 1) xs ys
  | _, _ => next

theorem lexNext_eq (next : Nat) (left right : List Nat) :
    lexNext next left right = next + (lexFreshIds next left right).length := by
  induction left generalizing right next with
  | nil => cases right <;> simp [lexNext, lexFreshIds]
  | cons x xs ih =>
      cases right with
      | nil => simp [lexNext, lexFreshIds]
      | cons y ys =>
          by_cases hxy : x = y
          · simp [lexNext, lexFreshIds, hxy, ih]
          · simp [lexNext, lexFreshIds, hxy, ih, Nat.add_assoc, Nat.add_comm]

/-- The permuted deletion-vector variables, using the permutation's indices as
the Python list comprehension does. Valid permutations have in-range indices. -/
def permutationVariables (deleted permutation : List Nat) : List Nat :=
  permutation.map fun i => deleted[i]!

/-- Concatenate the exact lex clauses for every permutation, threading the
fresh-variable counter across comparisons as the encoder does. -/
def orbitLexClauses (truth next : Nat) (deleted : List Nat) :
    List (List Nat) → List (List Int)
  | [] => []
  | permutation :: rest =>
      let image := permutationVariables deleted permutation
      lexClauses truth next deleted image ++
        orbitLexClauses truth (lexNext next deleted image) deleted rest

/-- Final unused variable after all lex comparisons in an orbit list. -/
def orbitLexNext (next : Nat) (deleted : List Nat) : List (List Nat) → Nat
  | [] => next
  | permutation :: rest =>
      let image := permutationVariables deleted permutation
      orbitLexNext (lexNext next deleted image) deleted rest

/-- Number of non-skipped positions over a list of permutations. -/
def orbitLexFreshCount (deleted : List Nat) : List (List Nat) → Nat
  | [] => 0
  | permutation :: rest =>
      (lexFreshIds 0 deleted (permutationVariables deleted permutation)).length +
        orbitLexFreshCount deleted rest

theorem orbitLexNext_eq (next : Nat) (deleted : List Nat) (permutations : List (List Nat)) :
    orbitLexNext next deleted permutations = next + orbitLexFreshCount deleted permutations := by
  induction permutations generalizing next with
  | nil => simp [orbitLexNext, orbitLexFreshCount]
  | cons permutation rest ih =>
      simp only [orbitLexNext, orbitLexFreshCount]
      rw [ih]
      rw [lexNext_eq]
      simp_rw [lexFreshIds_length]
      omega

/-- Identical DIMACS variables have the same assigned bit, which justifies
skipping that position without an auxiliary equality gate. -/
theorem identical_variables_same_value (a : Nat → Bool) {x y : Nat}
    (hxy : x = y) : a x = a y := by
  subst y
  rfl

/-- DIMACS clauses for an equality-prefix gate are satisfied when `same` is
assigned the exact prefix conjunction. -/
theorem lexStep_auxiliary_assignment_satisfies (a : Nat → Bool)
    (pref x y same : Nat) (hp0 : 0 < pref) (hx0 : 0 < x)
    (hy0 : 0 < y) (hs0 : 0 < same)
    (hguard : (!a pref || a x || !a y) = true)
    (hs : a same = (a pref && (a x == a y))) :
    cnfValue a (lexStepClauses pref x y same) = true := by
  simp only [cnfValue, List.all_cons, List.all_nil, clauseValue, List.any_cons,
    List.any_nil, lexStepClauses]
  simp only [literalValue_neg a pref hp0, literalValue_neg a x hx0,
    literalValue_neg a y hy0, literalValue_neg a same hs0,
    literalValue_pos a pref hp0, literalValue_pos a x hx0,
    literalValue_pos a y hy0, literalValue_pos a same hs0]
  cases hp : a pref <;> cases hx : a x <;> cases hy : a y <;>
    simp_all [pos, hguard, hs]

/-- A satisfying assignment to the comparison clauses extends the input
assignment by setting the fresh prefix variable to the equality-prefix value. -/
theorem lexStep_extension (a : Nat → Bool) (pref x y same : Nat)
    (hp0 : 0 < pref) (hx0 : 0 < x) (hy0 : 0 < y) (hs0 : 0 < same)
    (hguard : (!a pref || a x || !a y) = true)
    (hps : pref ≠ same) (hxs : x ≠ same) (hys : y ≠ same) :
    ∃ b : Nat → Bool, (∀ n, n ≠ same → b n = a n) ∧
      b same = (a pref && (a x == a y)) ∧
      cnfValue b (lexStepClauses pref x y same) = true := by
  let b := Function.update a same (a pref && (a x == a y))
  have hbp : b pref = a pref := by simp [b, Function.update, hps]
  have hbx : b x = a x := by simp [b, Function.update, hxs]
  have hby : b y = a y := by simp [b, Function.update, hys]
  have hguardB : (!b pref || b x || !b y) = true := by
    simpa [hbp, hbx, hby] using hguard
  have hsame : b same = (a pref && (a x == a y)) := by
    simp [b, Function.update]
  refine ⟨b, ?_, hsame, ?_⟩
  · intro n hns
    simp [b, Function.update, hns]
  · rw [lexStep_auxiliary_assignment_satisfies b pref x y same hp0 hx0 hy0 hs0]
    · exact hguardB
    · simpa [hbp, hbx, hby] using hsame


theorem lexClauses_extend_of_constraint (a : Nat → Bool) (base : Nat)
    (initialPref : Bool) (prefVar : Nat) (left right : List Nat)
    (hlen : left.length = right.length)
    (hpref0 : 0 < prefVar) (hprefBase : prefVar < base)
    (hprefix : a prefVar = initialPref)
    (hleftPos : ∀ x ∈ left, 0 < x) (hrightPos : ∀ y ∈ right, 0 < y)
    (hleftBound : ∀ x ∈ left, x < base) (hrightBound : ∀ y ∈ right, y < base)
    (hconstraint : lexConstraint initialPref (left.map a) (right.map a) = true) :
    cnfValue (lexAssignment a base initialPref left right)
      (lexClauses prefVar base left right) = true := by
  induction left generalizing right base initialPref prefVar a with
  | nil =>
      cases right with
      | nil => simp [lexClauses, cnfValue]
      | cons y ys => simp at hlen
  | cons x xs ih =>
      cases right with
      | nil => simp at hlen
      | cons y ys =>
          simp only [List.length_cons, Nat.succ.injEq] at hlen
          have hxpos : 0 < x := hleftPos x (by simp)
          have hypos : 0 < y := hrightPos y (by simp)
          have hxbound : x < base := hleftBound x (by simp)
          have hybound : y < base := hrightBound y (by simp)
          have htailL : ∀ z ∈ xs, z < base := by
            intro z hz
            exact hleftBound z (by simp [hz])
          have htailR : ∀ z ∈ ys, z < base := by
            intro z hz
            exact hrightBound z (by simp [hz])
          have htailLp : ∀ z ∈ xs, 0 < z := by
            intro z hz
            exact hleftPos z (by simp [hz])
          have htailRp : ∀ z ∈ ys, 0 < z := by
            intro z hz
            exact hrightPos z (by simp [hz])
          by_cases hxy : x = y
          · subst y
            have hconstraint' :
                lexConstraint initialPref (xs.map a) (ys.map a) = true := by
              have h := (Bool.and_eq_true_iff.mp hconstraint).2
              simpa using h
            have hassign : lexAssignment a base initialPref (x :: xs) (x :: ys) =
                lexAssignment a base initialPref xs ys := by
              funext n
              simp [lexAssignment, lexPrefixScan]
            rw [hassign]
            simp only [lexClauses, beq_self_eq_true, ite_true]
            exact ih a base initialPref prefVar ys hlen hpref0 hprefBase hprefix
              htailLp htailRp htailL htailR hconstraint'
          · have hconstraint' :
                ((!initialPref || a x || !a y) &&
                  lexConstraint (initialPref && (a x == a y)) (xs.map a) (ys.map a)) = true := by
              change ((!initialPref || a x || !a y) &&
                lexConstraint (initialPref && (a x == a y)) (xs.map a) (ys.map a)) = true at hconstraint
              exact hconstraint
            rcases Bool.and_eq_true_iff.mp hconstraint' with ⟨hguard, htailConstraint⟩
            let nextPref := initialPref && (a x == a y)
            let g := lexAssignment a base initialPref (x :: xs) (y :: ys)
            have hgpref : g prefVar = initialPref := by
              dsimp [g]
              rw [lexAssignment_preserves_below_base a base initialPref (x :: xs) (y :: ys)
                hprefBase]
              exact hprefix
            have hgx : g x = a x := by
              dsimp [g]
              exact lexAssignment_preserves_below_base a base initialPref (x :: xs) (y :: ys) hxbound
            have hgy : g y = a y := by
              dsimp [g]
              exact lexAssignment_preserves_below_base a base initialPref (x :: xs) (y :: ys) hybound
            have hscanPos : 0 < (lexPrefixScan a initialPref (x :: xs) (y :: ys)).length := by
              simp [lexPrefixScan, hxy]
            have hgb : g base = nextPref := by
              dsimp [g]
              simpa [nextPref, lexPrefixScan, hxy] using
                (lexAssignment_fresh_id a base initialPref (x :: xs) (y :: ys)
                  (k := 0) (by simpa using hscanPos))
            have hstep : cnfValue g (lexStepClauses prefVar x y base) = true := by
              apply lexStep_auxiliary_assignment_satisfies g prefVar x y base hpref0 hxpos hypos
              · omega
              · simpa [hgpref, hgx, hgy] using hguard
              · simp [hgpref, hgx, hgy, hgb, nextPref]
            have hassign :
                lexAssignment a base initialPref (x :: xs) (y :: ys) =
                  lexAssignment (extendVariable a base nextPref) (base + 1)
                    nextPref xs ys := by
              simpa [nextPref] using
                lexAssignment_cons_neq a base initialPref x y xs ys hxy hxbound hybound htailL htailR
            have htailSat :
                cnfValue (lexAssignment (extendVariable a base nextPref) (base + 1)
                  nextPref xs ys) (lexClauses base (base + 1) xs ys) = true := by
              have hext (z : Nat) (hz : z < base) :
                  extendVariable a base nextPref z = a z := by
                simp [extendVariable, Nat.ne_of_lt hz]
              have hmapL : xs.map (extendVariable a base nextPref) = xs.map a :=
                List.map_congr_left (fun z hz => hext z (htailL z hz))
              have hmapR : ys.map (extendVariable a base nextPref) = ys.map a :=
                List.map_congr_left (fun z hz => hext z (htailR z hz))
              exact ih (extendVariable a base nextPref) (base + 1) nextPref base ys hlen
                (by omega) (by omega) (by simp [extendVariable]) htailLp htailRp
                (fun z hz => by have := htailL z hz; omega)
                (fun z hz => by have := htailR z hz; omega)
                (by simpa [hmapL, hmapR, nextPref] using htailConstraint)
            have htailSat' : cnfValue g (lexClauses base (base + 1) xs ys) = true := by
              dsimp [g]
              rw [hassign]
              exact htailSat
            simp only [lexClauses, ite_eq_right (show ¬ (x == y) = true by simpa using hxy)]
            simpa only [cnfValue, List.all_append, Bool.and_eq_true] using And.intro hstep htailSat'

/-- On equal-length lists, the encoder's comparator agrees with Lean's
lexicographic order on Boolean lists. -/
theorem lexAtLeast_eq_true_of_le (left right : List Bool)
    (hlen : left.length = right.length) (hle : right ≤ left) :
    lexAtLeast left right = true := by
  induction left generalizing right with
  | nil =>
    cases right with
    | nil => rfl
    | cons y ys => simp at hlen
  | cons x xs ih =>
    cases right with
    | nil => simp at hlen
    | cons y ys =>
      simp only [List.length_cons, Nat.succ.injEq] at hlen
      rw [le_iff_lt_or_eq] at hle
      rcases hle with hlt | heq
      · change List.Lex (· < ·) (y :: ys) (x :: xs) at hlt
        rcases List.cons_lex_cons_iff.mp hlt with hxy | ⟨heq, ht⟩
        · cases x <;> cases y <;> simp_all [lexAtLeast] <;> exact (by decide : ¬ true < false) hxy
        · subst y
          have ht' : ys < xs := ht
          simp [lexAtLeast, ih ys hlen ht'.le]
      · cases List.cons.inj heq with
        | intro hxy htail =>
          subst y
          subst ys
          simp [lexAtLeast, ih xs rfl le_rfl]

private theorem lexNext_ge (base : Nat) (left right : List Nat) :
    base ≤ lexNext base left right := by rw [lexNext_eq]; omega

private theorem lexClauses_ids_lt_next (pref base : Nat) (left right : List Nat)
    (hp : pref < base) (hl : ∀ v ∈ left, v < base) (hr : ∀ v ∈ right, v < base) :
    ∀ clause ∈ lexClauses pref base left right, ∀ l ∈ clause,
      l.natAbs < lexNext base left right := by
  induction left generalizing right pref base with
  | nil => cases right <;> simp [lexClauses]
  | cons x xs ih =>
    cases right with
    | nil => simp [lexClauses]
    | cons y ys =>
      have hx := hl x (by simp)
      have hy := hr y (by simp)
      have hxs v (hv : v ∈ xs) := hl v (by simp [hv])
      have hys v (hv : v ∈ ys) := hr v (by simp [hv])
      by_cases hxy : x = y
      · simpa [lexClauses, lexNext, hxy] using ih pref base ys hp hxs hys
      · simp only [lexClauses, lexNext, show (x == y) = false by simp [hxy], Bool.false_eq_true,
          ↓reduceIte]
        intro clause hc l hLit
        rcases List.mem_append.mp hc with hStep | hTail
        · have hb : base < lexNext (base + 1) xs ys :=
            lt_of_lt_of_le (by omega) (lexNext_ge (base + 1) xs ys)
          simp [lexStepClauses] at hStep
          rcases hStep with rfl | rfl | rfl | rfl | rfl | rfl <;>
            simp [pos, neg] at hLit <;> rcases hLit with rfl | rfl | rfl | rfl | rfl <;>
            (try simp only [pos, neg, Int.natAbs_negOfNat]) <;> omega
        · exact ih base (base + 1) ys (by omega)
            (fun v hv => Nat.lt_succ_of_lt (hxs v hv))
            (fun v hv => Nat.lt_succ_of_lt (hys v hv)) clause hTail l hLit

/-- Assign every fresh variable in every comparison, in the same order as
the encoder. The original deletion variables are retained at each step. -/
def orbitLexAssignment (truth next : Nat) (deleted : List Nat) :
    (Nat → Bool) → List (List Nat) → Nat → Bool
  | a, [] => a
  | a, permutation :: rest =>
    let image := permutationVariables deleted permutation
    orbitLexAssignment truth (lexNext next deleted image) deleted
      (lexAssignment a next (a truth) deleted image) rest

theorem orbitLexAssignment_preserves (truth next : Nat) (deleted : List Nat)
    (a : Nat → Bool) (permutations : List (List Nat)) (n : Nat) (hn : n < next) :
    orbitLexAssignment truth next deleted a permutations n = a n := by
  induction permutations generalizing next a with
  | nil => rfl
  | cons p ps ih =>
    simp only [orbitLexAssignment]
    rw [ih _ _ (lt_of_lt_of_le hn (lexNext_ge _ _ _))]
    exact lexAssignment_preserves_below_base _ _ _ _ _ hn

private theorem cnfValue_congr_of_bound (a b : Nat → Bool) (cs : List (List Int))
    (bound : Nat) (hab : ∀ n < bound, a n = b n)
    (hc : ∀ c ∈ cs, ∀ l ∈ c, l.natAbs < bound) :
    cnfValue a cs = cnfValue b cs := by
  unfold cnfValue
  apply Bool.eq_iff_iff.mpr
  simp only [List.all_eq_true]
  have heq (c : List Int) (hmem : c ∈ cs) : clauseValue a c = clauseValue b c := by
    unfold clauseValue
    apply Bool.eq_iff_iff.mpr
    simp only [List.any_eq_true]
    have hl (l : Int) (hm : l ∈ c) : literalValue a l = literalValue b l := by
      have hb := hc c hmem l hm
      cases l with
      | ofNat n => exact hab n hb
      | negSucc n =>
        change (!(a (n + 1))) = (!(b (n + 1)))
        rw [hab (n + 1) hb]
    exact ⟨fun ⟨l,hm,hv⟩ => ⟨l,hm,hl l hm ▸ hv⟩,
      fun ⟨l,hm,hv⟩ => ⟨l,hm,(hl l hm).symm ▸ hv⟩⟩
  exact ⟨fun h c hm => heq c hm ▸ h c hm, fun h c hm => (heq c hm).symm ▸ h c hm⟩

/-- A common valuation satisfies every signed lex clause in the generated
orbit, provided each input bit-vector comparison holds. -/
theorem orbitLexClauses_satisfied (truth next : Nat) (deleted : List Nat)
    (a : Nat → Bool) (permutations : List (List Nat))
    (ht0 : 0 < truth) (ht : truth < next) (hta : a truth = true)
    (hd : ∀ n ∈ deleted, 0 < n ∧ n < next)
    (hp : ∀ p ∈ permutations, p.length = deleted.length ∧
      (∀ i ∈ p, i < deleted.length) ∧
      lexAtLeast (deleted.map a) ((permutationVariables deleted p).map a) = true) :
    cnfValue (orbitLexAssignment truth next deleted a permutations)
      (orbitLexClauses truth next deleted permutations) = true := by
  induction permutations generalizing next a with
  | nil => rfl
  | cons p ps ih =>
    let image := permutationVariables deleted p
    let stop := lexNext next deleted image
    let b := lexAssignment a next true deleted image
    let out := orbitLexAssignment truth stop deleted b ps
    have hstop := lexNext_ge next deleted image
    have hpres {n : Nat} (hn : n < next) : b n = a n :=
      lexAssignment_preserves_below_base a next true deleted image hn
    have hvec (q : List Nat) (hq : ∀ i ∈ q, i < deleted.length) :
        ∀ n ∈ permutationVariables deleted q, 0 < n ∧ n < next := by
      intro n hn
      obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hn
      have hlt := hq i hi
      rw [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem hlt]
      exact hd _ (List.getElem_mem _)
    obtain ⟨hlen, hip, hlex⟩ := hp p (by simp)
    have hi := hvec p hip
    have hlen' : deleted.length = image.length := by simp [image, permutationVariables, hlen]
    have hcmp : lexConstraint true (deleted.map a) (image.map a) = true := by
      rw [lex_constraint_iff _ _ (by simpa using hlen')]
      exact hlex
    have hcurrent : cnfValue b (lexClauses truth next deleted image) = true :=
      lexClauses_extend_of_constraint a next true truth deleted image hlen'
        ht0 ht hta (fun n hn => (hd n hn).1) (fun n hn => (hi n hn).1)
        (fun n hn => (hd n hn).2) (fun n hn => (hi n hn).2) hcmp
    have hsat : cnfValue out (lexClauses truth next deleted image) = true := by
      rw [cnfValue_congr_of_bound out b _ stop
        (orbitLexAssignment_preserves truth stop deleted b ps)
        (lexClauses_ids_lt_next truth next deleted image ht
          (fun n hn => (hd n hn).2) (fun n hn => (hi n hn).2))]
      exact hcurrent
    have htail : cnfValue out (orbitLexClauses truth stop deleted ps) = true := by
      apply ih stop b (lt_of_lt_of_le ht hstop) ((hpres ht).trans hta)
      · exact fun n hn => ⟨(hd n hn).1, lt_of_lt_of_le (hd n hn).2 hstop⟩
      · intro q hq
        obtain ⟨hql,hqi,hqlex⟩ := hp q (by simp [hq])
        have hmap (l : List Nat) (hl : ∀ n ∈ l, n < next) :
            l.map b = l.map a := List.map_congr_left (fun n hn => hpres (hl n hn))
        refine ⟨hql,hqi,?_⟩
        rw [hmap deleted (fun n hn => (hd n hn).2),
          hmap _ (fun n hn => (hvec q hqi n hn).2)]
        exact hqlex
    simpa only [orbitLexAssignment, orbitLexClauses, hta, cnfValue, List.all_append,
      Bool.and_eq_true] using And.intro hsat htail

end Implications.C4PolarityLexEncoding

#print axioms Implications.C4PolarityLexEncoding.lexFreshIds_length
#print axioms Implications.C4PolarityLexEncoding.lexNext_eq
#print axioms Implications.C4PolarityLexEncoding.orbitLexNext_eq
#print axioms Implications.C4PolarityLexEncoding.lexStep_auxiliary_assignment_satisfies
#print axioms Implications.C4PolarityLexEncoding.lexStep_extension

#print axioms Implications.C4PolarityLexEncoding.lexClauses_extend_of_constraint

#print axioms Implications.C4PolarityLexEncoding.orbitLexClauses_satisfied
#print axioms Implications.C4PolarityLexEncoding.lexAtLeast_eq_true_of_le
