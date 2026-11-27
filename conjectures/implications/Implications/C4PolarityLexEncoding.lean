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

/-- A lexicographically admissible input assignment extends to all fresh
equality-prefix variables in the exact consecutive DIMACS block, satisfying
the complete comparison CNF. -/
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
  induction left generalizing right base initialPref prefVar with
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
          · have hconstraint' :
                lexConstraint initialPref (xs.map a) (ys.map a) = true := by
              simpa [lexConstraint, hxy] using hconstraint
            have hassign : lexAssignment a base initialPref (x :: xs) (y :: ys) =
                lexAssignment a base initialPref xs ys := by
              funext n
              simp [lexAssignment, lexPrefixScan, hxy]
            simpa [lexClauses, hxy, hassign] using
              (ih ys base initialPref prefVar rfl hpref0 hprefBase hprefix
                htailLp htailRp htailL htailR hconstraint')
          · have hconstraint' :
                ((!initialPref || a x || !a y) &&
                  lexConstraint (initialPref && (a x == a y)) (xs.map a) (ys.map a)) = true := by
              change ((!initialPref || a x || !a y) &&
                lexConstraint (initialPref && (a x == a y)) (xs.map a) (ys.map a)) = true at hconstraint
              exact hconstraint
            rcases Bool.and_eq_true.mp hconstraint' with ⟨hguard, htailConstraint⟩
            let nextPref := initialPref && (a x == a y)
            let g := lexAssignment a base initialPref (x :: xs) (y :: ys)
            have hgpref : g prefVar = initialPref := by
              dsimp [g]
              rw [lexAssignment_preserves_below_base a base initialPref (x :: xs) (y :: ys)
                (Nat.lt_trans hprefBase (by omega))]
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
              dsimp [g, nextPref]
              rw [lexAssignment_fresh_id a base initialPref (x :: xs) (y :: ys)
                (k := 0) (by simpa using hscanPos)]
              simp [lexPrefixScan, hxy]
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
              apply ih ys (base + 1) nextPref base hlen hpref0 ?_ ?_ htailLp htailRp ?_ ?_ htailConstraint
              · omega
              · simp [extendVariable]
              · intro z hz
                have := htailL z hz
                omega
              · intro z hz
                have := htailR z hz
                omega
            have htailSat' : cnfValue g (lexClauses base (base + 1) xs ys) = true := by
              simpa [hassign] using htailSat
            change cnfValue g (lexStepClauses prefVar x y base ++
              lexClauses base (base + 1) xs ys) = true
            simp [cnfValue, hstep, htailSat']

end Implications.C4PolarityLexEncoding

#print axioms Implications.C4PolarityLexEncoding.lexFreshIds_length
#print axioms Implications.C4PolarityLexEncoding.lexNext_eq
#print axioms Implications.C4PolarityLexEncoding.orbitLexNext_eq
#print axioms Implications.C4PolarityLexEncoding.lexStep_auxiliary_assignment_satisfies
#print axioms Implications.C4PolarityLexEncoding.lexStep_extension
