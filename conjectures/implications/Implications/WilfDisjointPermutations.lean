import Mathlib

/-! Reassembling finitely many permutations with pairwise disjoint supports. -/

namespace Implications.WilfDisjointPermutations

/-- The product of a pairwise-disjoint finite family of permutations. -/
def assemble {ι α : Type*} [DecidableEq ι] [DecidableEq α] (s : Finset ι)
    (k : ι → Equiv.Perm α)
    (hdisj : (s : Set ι).Pairwise fun i j => Equiv.Perm.Disjoint (k i) (k j)) :
    Equiv.Perm α :=
  s.noncommProd k (hdisj.imp fun _ _ => Equiv.Perm.Disjoint.commute)

/-- On the support of one component, the assembled permutation acts as that component. -/
theorem assemble_apply_of_mem_support {ι α : Type*} [DecidableEq ι] [DecidableEq α]
    (s : Finset ι) (k : ι → Equiv.Perm α)
    (hdisj : (s : Set ι).Pairwise fun i j => Equiv.Perm.Disjoint (k i) (k j))
    {i : ι} (hi : i ∈ s) {x : α} (hx : x ∈ (k i).support) :
    assemble s k hdisj x = k i x := by
  classical
  have hcomm : (s : Set ι).Pairwise fun i j => Commute (k i) (k j) :=
    hdisj.imp fun _ _ => Equiv.Perm.Disjoint.commute
  have hrest_comm : (s.erase i : Set ι).Pairwise fun j l => Commute (k j) (k l) := by
    intro j hj l hl hne
    have hj' : j ∈ s := Finset.mem_of_mem_erase hj
    have hl' : l ∈ s := Finset.mem_of_mem_erase hl
    exact hcomm j hj' l hl' hne
  have hxne : k i x ≠ x := by simpa using hx
  have hrest_fixes : ∀ j ∈ s.erase i, k j x = x := by
    intro j hj
    rcases Finset.mem_erase.mp hj with ⟨hji, hjs⟩
    rcases hdisj j hjs i hi hji with hjfix | hifix
    · exact hjfix
    · exact (hxne hifix).elim
  have hrest : (s.erase i).noncommProd k hrest_comm x = x :=
    Finset.noncommProd_induction _ _ hrest_comm (fun f : Equiv.Perm α => f x = x)
      (fun f g hf hg => by simp [Equiv.Perm.mul_apply, hf, hg])
      rfl hrest_fixes
  rw [assemble, ← Finset.insert_erase hi,
    Finset.noncommProd_insert_of_notMem _ _ _ _ (Finset.not_mem_erase i s)]
  simp only [Equiv.Perm.mul_apply, hrest]

/-- Away from every component support, the assembled permutation fixes the point. -/
theorem assemble_apply_of_forall_fixes {ι α : Type*} [DecidableEq ι] [DecidableEq α]
    (s : Finset ι) (k : ι → Equiv.Perm α)
    (hdisj : (s : Set ι).Pairwise fun i j => Equiv.Perm.Disjoint (k i) (k j))
    {x : α} (hfix : ∀ i ∈ s, k i x = x) :
    assemble s k hdisj x = x := by
  classical
  have hcomm : (s : Set ι).Pairwise fun i j => Commute (k i) (k j) :=
    hdisj.imp fun _ _ => Equiv.Perm.Disjoint.commute
  exact Finset.noncommProd_induction s k hcomm (fun f : Equiv.Perm α => f x = x)
    (fun f g hf hg => by simp [Equiv.Perm.mul_apply, hf, hg])
    rfl hfix

/-- A point outside the union of the component supports is fixed by the assembly. -/
theorem assemble_apply_of_not_mem_support {ι α : Type*} [DecidableEq ι] [DecidableEq α]
    (s : Finset ι) (k : ι → Equiv.Perm α)
    (hdisj : (s : Set ι).Pairwise fun i j => Equiv.Perm.Disjoint (k i) (k j))
    {x : α} (hx : x ∉ s.biUnion fun i => (k i).support) :
    assemble s k hdisj x = x := by
  apply assemble_apply_of_forall_fixes s k hdisj
  intro i hi
  have hnot : x ∉ (k i).support := by
    intro hmem
    exact hx (Finset.mem_biUnion.mpr ⟨i, hi, hmem⟩)
  simpa using hnot

/-- The support of the assembled permutation is exactly the union of the component supports. -/
theorem assemble_support {ι α : Type*} [DecidableEq ι] [DecidableEq α]
    (s : Finset ι) (k : ι → Equiv.Perm α)
    (hdisj : (s : Set ι).Pairwise fun i j => Equiv.Perm.Disjoint (k i) (k j)) :
    (assemble s k hdisj).support = s.biUnion fun i => (k i).support := by
  exact Equiv.Perm.support_noncommProd hdisj

end Implications.WilfDisjointPermutations
