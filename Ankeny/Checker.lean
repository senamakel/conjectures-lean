import Mathlib

/-!
# A verified generation checker for `(ZMod q)ˣ`

`checkGen q y` runs a breadth-first search from `1` in `ZMod q`, multiplying by a few small
generators `g ≤ y` coprime to `q`, and then checks that every residue coprime to `q` was
reached. Soundness (`closure_eq_top_of_checkGen`): if it returns `true`, the units of residue
`≤ y` generate `(ZMod q)ˣ`.

The search only ever marks `1` or `r * g % q` with `r` already marked, so every marked residue
is a product of generators; that invariant is all the soundness proof uses (fuel, the order of
the search and the choice of generators matter only for completeness).
-/

namespace Ankeny.Checker

/-- Is index `i` marked? -/
def marked (arr : Array Bool) (i : ℕ) : Bool := arr[i]?.getD false

/-- Multiply `r` by every generator; mark and enqueue the new residues. -/
def bfsStep (q : ℕ) (gens : List ℕ) (r : ℕ) (st : Array Bool × List ℕ) : Array Bool × List ℕ :=
  gens.foldl (fun acc g =>
    let t := r * g % q
    if marked acc.1 t then acc else (acc.1.setIfInBounds t true, t :: acc.2)) st

/-- Breadth-first (well, depth-first) search with fuel. -/
def bfs (q : ℕ) (gens : List ℕ) : ℕ → Array Bool → List ℕ → Array Bool
  | 0, arr, _ => arr
  | _ + 1, arr, [] => arr
  | n + 1, arr, r :: rest =>
    let st := bfsStep q gens r (arr, rest)
    bfs q gens n st.1 st.2

/-- Candidate generators: the first `k` primes `≤ y` (and `< q`) coprime to `q`. -/
def gensFor (q y k : ℕ) : List ℕ :=
  (((List.range (min (y + 1) q)).filter fun g => 2 ≤ g && g.minFac == g && Nat.gcd g q == 1)).take k

/-- Does the search from `1` with generators `gens` reach every residue coprime to `q`? -/
def reachesAll (q : ℕ) (gens : List ℕ) : Bool :=
  let arr := bfs q gens (q + 1) ((Array.replicate q false).setIfInBounds 1 true) [1]
  (List.range q).all fun a => Nat.gcd a q != 1 || marked arr a

/-- The checker: try 3 generators, then 8, then all candidates. -/
def checkGen (q y : ℕ) : Bool :=
  reachesAll q (gensFor q y 3) || reachesAll q (gensFor q y 8) || reachesAll q (gensFor q y q)

/-! ### Soundness -/

section Sound

variable (q : ℕ) (gens : List ℕ) (Good : ℕ → Prop)

/-- The search invariant: every marked index and every queued index is good. -/
def Inv (st : Array Bool × List ℕ) : Prop :=
  (∀ i, marked st.1 i = true → Good i) ∧ ∀ i ∈ st.2, Good i

lemma marked_setIfInBounds (arr : Array Bool) (t i : ℕ) (h : marked (arr.setIfInBounds t true) i) :
    i = t ∨ marked arr i = true := by
  unfold marked at *
  rw [Array.getElem?_setIfInBounds] at h
  by_cases hti : t = i
  · exact Or.inl hti.symm
  · simp only [hti, ite_false] at h
    exact Or.inr h

lemma inv_foldl (r : ℕ) (gs : List ℕ) (hgs : ∀ g ∈ gs, Good (r * g % q))
    (st : Array Bool × List ℕ) (hst : Inv Good st) :
    Inv Good (gs.foldl (fun acc g =>
      let t := r * g % q
      if marked acc.1 t then acc else (acc.1.setIfInBounds t true, t :: acc.2)) st) := by
  induction gs generalizing st with
  | nil => exact hst
  | cons g gs ih =>
    rw [List.foldl_cons]
    apply ih (fun g' hg' => hgs g' (List.mem_cons_of_mem _ hg'))
    have hg := hgs g List.mem_cons_self
    dsimp only
    split_ifs
    · exact hst
    · refine ⟨fun i hi => ?_, fun i hi => ?_⟩
      · rcases marked_setIfInBounds _ _ _ hi with h | h
        · exact h ▸ hg
        · exact hst.1 i h
      · rcases List.mem_cons.1 hi with h | h
        · exact h ▸ hg
        · exact hst.2 i h

lemma inv_bfs (hmul : ∀ r g, Good r → g ∈ gens → Good (r * g % q)) :
    ∀ (n : ℕ) (arr : Array Bool) (l : List ℕ), Inv Good (arr, l) →
      ∀ i, marked (bfs q gens n arr l) i = true → Good i
  | 0, arr, l, h => by simpa [bfs] using h.1
  | n + 1, arr, [], h => by simpa [bfs] using h.1
  | n + 1, arr, r :: rest, h => by
    rw [bfs]
    have hr : Good r := h.2 r List.mem_cons_self
    have h' : Inv Good (arr, rest) := ⟨h.1, fun i hi => h.2 i (List.mem_cons_of_mem _ hi)⟩
    have := inv_foldl q Good r gens (fun g hg => hmul r g hr hg) (arr, rest) h'
    exact inv_bfs hmul n _ _ this

end Sound

/-- The units of residue `≤ y`. -/
def smallUnits (q y : ℕ) : Set (ZMod q)ˣ := {u | (u : ZMod q).val ≤ y}

lemma mem_gensFor {q y k g : ℕ} (h : g ∈ gensFor q y k) : g.Coprime q ∧ g ≤ y := by
  have h' := List.mem_of_mem_take h
  simp only [List.mem_filter, List.mem_range, Bool.and_eq_true, beq_iff_eq,
    decide_eq_true_eq] at h'
  exact ⟨h'.2.2, by omega⟩

lemma closure_eq_top_of_reachesAll (q y : ℕ) [NeZero q] (gens : List ℕ)
    (hgens : ∀ g ∈ gens, g.Coprime q ∧ g ≤ y) (h : reachesAll q gens = true) :
    Subgroup.closure (smallUnits q y) = ⊤ := by
  set K := Subgroup.closure (smallUnits q y)
  let Good : ℕ → Prop := fun i => ∃ u ∈ K, (u : ZMod q) = (i : ZMod q)
  have hmul : ∀ r g, Good r → g ∈ gens → Good (r * g % q) := by
    rintro r g ⟨u, hu, hur⟩ hg
    obtain ⟨hcop, hgy⟩ := hgens g hg
    refine ⟨u * ZMod.unitOfCoprime g hcop, K.mul_mem hu (Subgroup.subset_closure ?_), ?_⟩
    · change (ZMod.unitOfCoprime g hcop : ZMod q).val ≤ y
      simp only [ZMod.coe_unitOfCoprime, ZMod.val_natCast]
      exact (Nat.mod_le _ _).trans hgy
    · simp [hur]
  have hinit : Inv Good ((Array.replicate q false).setIfInBounds 1 true, [1]) := by
    refine ⟨fun i hi => ?_, fun i hi => ?_⟩
    · rcases marked_setIfInBounds _ _ _ hi with h | h
      · exact ⟨1, K.one_mem, by simp [h]⟩
      · simp only [marked, Array.getElem?_replicate] at h
        split_ifs at h <;> simp at h
    · rw [List.mem_singleton.1 hi]
      exact ⟨1, K.one_mem, by simp⟩
  have hreach := inv_bfs q gens Good hmul (q + 1) _ _ hinit
  unfold reachesAll at h
  rw [List.all_eq_true] at h
  rw [eq_top_iff]
  intro v _
  have hv := h (v : ZMod q).val (List.mem_range.2 (ZMod.val_lt _))
  have hcop : Nat.gcd (v : ZMod q).val q = 1 := ZMod.val_coe_unit_coprime v
  simp only [hcop, bne_self_eq_false, Bool.false_or] at hv
  obtain ⟨u, hu, huv⟩ := hreach _ hv
  rw [ZMod.natCast_zmod_val] at huv
  rwa [Units.ext huv] at hu

theorem closure_eq_top_of_checkGen (q y : ℕ) [NeZero q] (h : checkGen q y = true) :
    Subgroup.closure (smallUnits q y) = ⊤ := by
  unfold checkGen at h
  simp only [Bool.or_eq_true] at h
  rcases h with (h | h) | h <;>
    exact closure_eq_top_of_reachesAll q y _ (fun g hg => mem_gensFor hg) h

end Ankeny.Checker
