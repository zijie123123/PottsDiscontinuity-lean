/- Adapted from an earlier, unpublished formalization of the planar FK model by the same author.
Parameter generalization: independent 0 < p < 1 and 1 ≤ q, with no upper bound on q. -/
module

public import PottsDiscontinuity.FK.ComponentMerge
public import PottsDiscontinuity.FK.FrozenBridge

/-!
# Supermodularity of the actual wired component count

Opening one edge merges two components precisely when its endpoints are not
already identified. More open edges can only make those endpoints more likely
to be identified. The corresponding diminishing component loss is summed along
finite edge additions to obtain the FK lattice condition's counting input.
-/

@[expose] public section

namespace PottsDiscontinuity.FK

variable {V : Type*} [Finite V] {G : SimpleGraph V} [DecidableEq G.edgeSet]

theorem componentCount_insert_increment_mono (ξ : BoundaryCondition V)
    (A B : Configuration G) (hAB : A ⊆ B) (e : G.edgeSet) :
    componentCount G ξ (insert e A) + componentCount G ξ B ≤
      componentCount G ξ (insert e B) + componentCount G ξ A := by
  obtain ⟨⟨u,v⟩,he⟩ := Sym2.mk_surjective e.val
  have he0 : s(u,v) = e.val := he
  have huv : G.Adj u v := G.mem_edgeSet.mp (by rw [he0]; exact e.property)
  have he' : e = ⟨s(u,v),G.mem_edgeSet.mpr huv⟩ := Subtype.ext he.symm
  subst e
  by_cases hA : (componentSetoid G ξ A).r u v
  · rw [componentCount_insert_eq_of_related ξ A huv hA,
      componentCount_insert_eq_of_related ξ B huv (componentSetoid_mono ξ hAB hA)]
    omega
  · have ha := componentCount_insert_of_not_related ξ A huv hA
    by_cases hB : (componentSetoid G ξ B).r u v
    · rw [componentCount_insert_eq_of_related ξ B huv hB]
      omega
    · have hb := componentCount_insert_of_not_related ξ B huv hB
      omega

/-- The loss from adding any common finite set of edges decreases when the
initial open configuration is larger. No subtraction conventions are needed. -/
theorem componentCount_union_increment_mono (ξ : BoundaryCondition V)
    (A B : Configuration G) (hAB : A ⊆ B) (C : Configuration G) :
    componentCount G ξ (A ∪ C) + componentCount G ξ B ≤
      componentCount G ξ (B ∪ C) + componentCount G ξ A := by
  induction C using Finset.induction_on with
  | empty => simp [add_comm]
  | @insert e C he ih =>
    have hsub : A ∪ C ⊆ B ∪ C := Finset.union_subset_union_left hAB
    have hi := componentCount_insert_increment_mono ξ (A ∪ C) (B ∪ C) hsub e
    simp only [Finset.union_insert] at *
    omega

/-- The exact wired component count is supermodular on the finite edge lattice. -/
theorem componentCount_supermodular (ξ : BoundaryCondition V) (A B : Configuration G) :
    componentCount G ξ A + componentCount G ξ B ≤
      componentCount G ξ (A ∩ B) + componentCount G ξ (A ∪ B) := by
  have h := componentCount_union_increment_mono ξ (A ∩ B) B Finset.inter_subset_right A
  have hi : A ∩ B ∪ A = A := Finset.union_eq_right.mpr Finset.inter_subset_left
  simpa only [hi, Finset.union_comm B A, add_comm] using h

end PottsDiscontinuity.FK
