import Cramer.CMS.Assembly

/-!
# Gluing checked windows

The cell list is cut into windows of eleven entries, consecutive windows sharing one entry, so
that each window is checked by `decide` in its own module (`CramerCompute.CMSData`). Here:
`glue` puts the windows back together, the checks of the windows give the checks of the glued
list (`chk_glue`, `chainB_glue`), and the pair sums add up (`pairSum_glue`). `pairSum_eq` turns a
pair sum into the index sum used by `Cramer.CMS.zeroSum_le`.
-/

namespace Cramer.CMS

open Finset
open CramerCompute (Ent chk chainB pairSum endOK posOK boundOK)

/-- Glue windows that share their boundary entries. -/
def glue : List (List Ent) → List Ent
  | [] => []
  | [w] => w
  | w :: v :: ws => w.dropLast ++ glue (v :: ws)

/-- Consecutive windows share an entry. -/
def Linked (ws : List (List Ent)) : Prop := List.IsChain (fun w v => w.getLast? = v.head?) ws

lemma chk_append_cons (qs : List ℤ) (GD : ℕ) :
    ∀ (A : List Ent) (a : Ent) (B : List Ent), chk qs GD (A ++ [a]) = true →
      chk qs GD (a :: B) = true → chk qs GD (A ++ a :: B) = true
  | [], _, _, _, h2 => h2
  | [x], a, B, h1, h2 => by
    simp only [List.cons_append, List.nil_append, CramerCompute.chk, Bool.and_eq_true] at h1 ⊢
    exact ⟨⟨⟨h1.1.1.1, h1.1.1.2⟩, h1.1.2⟩, h2⟩
  | x :: y :: A, a, B, h1, h2 => by
    simp only [List.cons_append, CramerCompute.chk, Bool.and_eq_true] at h1 ⊢
    exact ⟨h1.1, chk_append_cons qs GD (y :: A) a B (by simpa using h1.2) h2⟩

lemma chainB_append_cons (P : Ent → Ent → Bool) :
    ∀ (A : List Ent) (a : Ent) (B : List Ent), chainB P (A ++ [a]) = true →
      chainB P (a :: B) = true → chainB P (A ++ a :: B) = true
  | [], _, _, _, h2 => h2
  | [x], a, B, h1, h2 => by
    simp only [List.cons_append, List.nil_append, CramerCompute.chainB, Bool.and_eq_true] at h1 ⊢
    exact ⟨h1.1, h2⟩
  | x :: y :: A, a, B, h1, h2 => by
    simp only [List.cons_append, CramerCompute.chainB, Bool.and_eq_true] at h1 ⊢
    exact ⟨h1.1, chainB_append_cons P (y :: A) a B (by simpa using h1.2) h2⟩

lemma pairSum_append_cons (f : Ent → Ent → ℕ) :
    ∀ (A : List Ent) (a : Ent) (B : List Ent),
      pairSum f (A ++ a :: B) = pairSum f (A ++ [a]) + pairSum f (a :: B)
  | [], a, B => by simp [CramerCompute.pairSum]
  | [x], a, B => by simp [CramerCompute.pairSum]
  | x :: y :: A, a, B => by
    simp only [List.cons_append, CramerCompute.pairSum]
    rw [show y :: (A ++ a :: B) = (y :: A) ++ a :: B by rfl, pairSum_append_cons f (y :: A) a B]
    simp only [List.cons_append]; ring

/-- A window and its last entry. -/
lemma eq_dropLast_append {w : List Ent} {a : Ent} (h : w.getLast? = some a) :
    w = w.dropLast ++ [a] := by
  have hw : w ≠ [] := by rintro rfl; simp at h
  rw [List.getLast?_eq_some_getLast hw, Option.some.injEq] at h
  rw [← h]; exact (List.dropLast_append_getLast hw).symm

lemma glue_cons_cons (w v : List Ent) (ws : List (List Ent)) :
    glue (w :: v :: ws) = w.dropLast ++ glue (v :: ws) := rfl

lemma glue_head (v : List Ent) (hv : 2 ≤ v.length) (ws : List (List Ent)) :
    (glue (v :: ws)).head? = v.head? := by
  cases ws with
  | nil => rfl
  | cons u us =>
    rw [glue_cons_cons]
    rcases v with _ | ⟨a, _ | ⟨b, l⟩⟩
    · simp at hv
    · simp at hv
    · simp

/-- `head? = some a` splits off the head. -/
lemma eq_cons_of_head? {L : List Ent} {a : Ent} (h : L.head? = some a) : L = a :: L.tail := by
  cases L with
  | nil => simp at h
  | cons b l => simp at h; rw [h]; rfl

/-- **Gluing a Boolean chain check.** -/
theorem chk_glue (qs : List ℤ) (GD : ℕ) : ∀ ws : List (List Ent), (∀ w ∈ ws, 2 ≤ w.length) →
    Linked ws → (∀ w ∈ ws, chk qs GD w = true) → chk qs GD (glue ws) = true
  | [], _, _, _ => rfl
  | [w], _, _, h => h w (by simp)
  | w :: v :: rest, hl, hlink, h => by
    rw [glue_cons_cons]
    have hlink' : Linked (v :: rest) := List.IsChain.tail hlink
    have hl' : ∀ x ∈ v :: rest, 2 ≤ x.length := fun x hx => hl x (List.mem_cons_of_mem _ hx)
    have hrest := chk_glue qs GD (v :: rest) hl' hlink' (fun x hx => h x (List.mem_cons_of_mem _ hx))
    have hwv : w.getLast? = v.head? := (List.isChain_cons_cons.1 hlink).1
    have hvne : v.head?.isSome := by
      rcases v with _ | ⟨a, l⟩
      · exact absurd (hl' [] (by simp)) (by simp)
      · simp
    obtain ⟨a, ha⟩ := Option.isSome_iff_exists.1 hvne
    have hg := glue_head v (hl' v (by simp)) rest
    rw [ha] at hg hwv
    rw [eq_cons_of_head? hg] at hrest ⊢
    refine chk_append_cons qs GD _ a _ ?_ hrest
    rw [← eq_dropLast_append hwv]; exact h w (by simp)

/-- **Gluing a pair check.** -/
theorem chainB_glue (P : Ent → Ent → Bool) : ∀ ws : List (List Ent), (∀ w ∈ ws, 2 ≤ w.length) →
    Linked ws → (∀ w ∈ ws, chainB P w = true) → chainB P (glue ws) = true
  | [], _, _, _ => rfl
  | [w], _, _, h => h w (by simp)
  | w :: v :: rest, hl, hlink, h => by
    rw [glue_cons_cons]
    have hlink' : Linked (v :: rest) := List.IsChain.tail hlink
    have hl' : ∀ x ∈ v :: rest, 2 ≤ x.length := fun x hx => hl x (List.mem_cons_of_mem _ hx)
    have hrest := chainB_glue P (v :: rest) hl' hlink' (fun x hx => h x (List.mem_cons_of_mem _ hx))
    have hwv : w.getLast? = v.head? := (List.isChain_cons_cons.1 hlink).1
    have hvne : v.head?.isSome := by
      rcases v with _ | ⟨a, l⟩
      · exact absurd (hl' [] (by simp)) (by simp)
      · simp
    obtain ⟨a, ha⟩ := Option.isSome_iff_exists.1 hvne
    have hg := glue_head v (hl' v (by simp)) rest
    rw [ha] at hg hwv
    rw [eq_cons_of_head? hg] at hrest ⊢
    refine chainB_append_cons P _ a _ ?_ hrest
    rw [← eq_dropLast_append hwv]; exact h w (by simp)

/-- **Pair sums add up.** -/
theorem pairSum_glue (f : Ent → Ent → ℕ) : ∀ ws : List (List Ent), (∀ w ∈ ws, 2 ≤ w.length) →
    Linked ws → pairSum f (glue ws) = (ws.map (pairSum f)).sum
  | [], _, _ => rfl
  | [w], _, _ => by simp [glue]
  | w :: v :: rest, hl, hlink => by
    rw [glue_cons_cons]
    have hlink' : Linked (v :: rest) := List.IsChain.tail hlink
    have hl' : ∀ x ∈ v :: rest, 2 ≤ x.length := fun x hx => hl x (List.mem_cons_of_mem _ hx)
    have hrest := pairSum_glue f (v :: rest) hl' hlink'
    have hwv : w.getLast? = v.head? := (List.isChain_cons_cons.1 hlink).1
    have hvne : v.head?.isSome := by
      rcases v with _ | ⟨a, l⟩
      · exact absurd (hl' [] (by simp)) (by simp)
      · simp
    obtain ⟨a, ha⟩ := Option.isSome_iff_exists.1 hvne
    have hg := glue_head v (hl' v (by simp)) rest
    rw [ha] at hg hwv
    rw [eq_cons_of_head? hg] at hrest ⊢
    rw [pairSum_append_cons, ← eq_dropLast_append hwv, hrest]
    simp

/-- The glued list has at least two entries. -/
lemma two_le_length_glue : ∀ ws : List (List Ent), ws ≠ [] → (∀ w ∈ ws, 2 ≤ w.length) →
    2 ≤ (glue ws).length
  | [], h, _ => absurd rfl h
  | [w], _, hl => hl w (by simp)
  | w :: v :: rest, _, hl => by
    rw [glue_cons_cons, List.length_append]
    have := two_le_length_glue (v :: rest) (by simp) (fun x hx => hl x (List.mem_cons_of_mem _ hx))
    omega

/-- **Pair sums are index sums.** -/
lemma pairSum_eq (f : Ent → Ent → ℕ) : ∀ L : List Ent,
    (pairSum f L : ℝ) = ∑ i ∈ range (L.length - 1), (f (L.getD i default) (L.getD (i + 1) default) : ℝ)
  | [] => by simp [CramerCompute.pairSum]
  | [a] => by simp [CramerCompute.pairSum]
  | a :: b :: l => by
    rw [CramerCompute.pairSum, Nat.cast_add, pairSum_eq f (b :: l)]
    simp only [List.length_cons, Nat.add_sub_cancel]
    rw [sum_range_succ']
    simp only [List.getD_cons_succ, List.getD_cons_zero]
    rw [add_comm]

/-- The last entry of a glued list. -/
lemma glue_getLast? : ∀ ws : List (List Ent), (∀ w ∈ ws, 2 ≤ w.length) → ws ≠ [] →
    (glue ws).getLast? = (ws.getLast?.bind List.getLast?)
  | [], _, h => absurd rfl h
  | [w], _, _ => by simp [glue]
  | w :: v :: rest, hl, _ => by
    rw [glue_cons_cons]
    have hl' : ∀ x ∈ v :: rest, 2 ≤ x.length := fun x hx => hl x (List.mem_cons_of_mem _ hx)
    have ih := glue_getLast? (v :: rest) hl' (by simp)
    have hne : glue (v :: rest) ≠ [] := by
      have := two_le_length_glue (v :: rest) (by simp) hl'
      intro h; rw [h] at this; simp at this
    rw [List.getLast?_append_of_ne_nil _ hne, ih]
    simp

lemma getD_last_eq {L : List Ent} {a : Ent} (h : L.getLast? = some a) :
    L.getD (L.length - 1) default = a := by
  have hne : L ≠ [] := by rintro rfl; simp at h
  rw [List.getLast?_eq_some_getLast hne, Option.some.injEq] at h
  rw [List.getD_eq_getElem _ _ (by have := List.length_pos_of_ne_nil hne; omega), ← h,
    List.getLast_eq_getElem]

lemma getD_zero_eq {L : List Ent} {a : Ent} (h : L.head? = some a) : L.getD 0 default = a := by
  cases L with
  | nil => simp at h
  | cons b l => simp at h; simp [h]

end Cramer.CMS
