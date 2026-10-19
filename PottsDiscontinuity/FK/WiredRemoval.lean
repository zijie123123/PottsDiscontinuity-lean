/- Adapted from an earlier, unpublished formalization of the planar FK model by the same author.
Parameter generalization: independent 0 < p < 1 and 1 ≤ q, with no upper bound on q. -/
module

public import Mathlib.Algebra.BigOperators.Ring.Finset
public import PottsDiscontinuity.FK.PositiveAssociation

/-!
# Removing finitely many prewired edges

For a finite set `R` of original graph edges, configurations split uniquely
into the open edges outside `R` and those inside `R`. If each edge of `R` has
boundary-identified endpoints, the latter choices do not affect the component
count. Consequently the full FK weight factors into the FK weight on the
remaining sampled edges and an ordinary Bernoulli weight on `R`.
-/

@[expose] public section

namespace PottsDiscontinuity.FK

open scoped BigOperators

variable {V : Type*} (G : SimpleGraph V)

/-- Configurations on the original edges that remain sampled after removing `R`. -/
abbrev RemainingConfiguration (R : Configuration G) :=
  {A : Configuration G // Disjoint A R}

/-- Configurations of the edges in `R`. -/
abbrev RemovedConfiguration (R : Configuration G) :=
  {B : Configuration G // B ⊆ R}

instance remainingConfiguration_nonempty (R : Configuration G) :
    Nonempty (RemainingConfiguration G R) := ⟨⟨∅, Finset.disjoint_empty_left R⟩⟩

instance removedConfiguration_nonempty (R : Configuration G) :
    Nonempty (RemovedConfiguration G R) := ⟨⟨∅, Finset.empty_subset R⟩⟩

instance remainingConfiguration_finite [Finite V] (R : Configuration G) :
    Finite (RemainingConfiguration G R) := by
  let : Fintype G.edgeSet := Fintype.ofFinite G.edgeSet
  infer_instance

instance removedConfiguration_finite [Finite V] (R : Configuration G) :
    Finite (RemovedConfiguration G R) := by
  let : Fintype G.edgeSet := Fintype.ofFinite G.edgeSet
  infer_instance

variable [DecidableEq G.edgeSet]

/-- Splitting a full configuration into its open edges outside and inside `R`. -/
def configurationSplitEquiv (R : Configuration G) :
    Configuration G ≃ RemainingConfiguration G R × RemovedConfiguration G R where
  toFun C := (⟨C \ R, Finset.sdiff_disjoint⟩, ⟨C ∩ R, Finset.inter_subset_right⟩)
  invFun P := P.1.val ∪ P.2.val
  left_inv C := Finset.sdiff_union_inter C R
  right_inv P := by
    rcases P with ⟨A, B⟩
    apply Prod.ext
    · apply Subtype.ext
      change (A.val ∪ B.val) \ R = A.val
      rw [Finset.union_sdiff_distrib, Finset.sdiff_eq_empty_iff_subset.mpr B.property,
        Finset.union_empty]
      exact sdiff_eq_left.mpr A.property
    · apply Subtype.ext
      change (A.val ∪ B.val) ∩ R = B.val
      rw [Finset.union_inter_distrib_right,
        Finset.disjoint_iff_inter_eq_empty.mp A.property, Finset.empty_union]
      exact Finset.inter_eq_left.mpr B.property

@[simp] theorem configurationSplitEquiv_symm_apply (R : Configuration G)
    (A : RemainingConfiguration G R) (B : RemovedConfiguration G R) :
    (configurationSplitEquiv G R).symm (A, B) = A.val ∪ B.val := rfl

omit [DecidableEq G.edgeSet] in
theorem remaining_disjoint_removed (R : Configuration G)
    (A : RemainingConfiguration G R) (B : RemovedConfiguration G R) :
    Disjoint A.val B.val := A.property.mono_right B.property

theorem remaining_card_add_removedSet_card_le [Finite V] (R : Configuration G)
    (A : RemainingConfiguration G R) : A.val.card + R.card ≤ Nat.card G.edgeSet := by
  let : Fintype G.edgeSet := Fintype.ofFinite G.edgeSet
  rw [← Finset.card_union_of_disjoint A.property, Nat.card_eq_fintype_card]
  exact Finset.card_le_univ _

omit [DecidableEq G.edgeSet] in
theorem removed_card_le (R : Configuration G) (B : RemovedConfiguration G R) :
    B.val.card ≤ R.card := Finset.card_le_card B.property

/-- Adding any collection of boundary-identified edges preserves all component
classes, even before imposing disjointness from the initial configuration. -/
theorem componentSetoid_union_removed (ξ : BoundaryCondition V) (R : Configuration G)
    (hR : ∀ (u v : V) (huv : G.Adj u v),
      (⟨s(u, v), G.mem_edgeSet.mpr huv⟩ : G.edgeSet) ∈ R → ξ.partition.r u v)
    (A : Configuration G) (B : RemovedConfiguration G R) :
    componentSetoid G ξ (A ∪ B.val) = componentSetoid G ξ A := by
  have haux : ∀ (S : Configuration G), S ⊆ R →
      componentSetoid G ξ (A ∪ S) = componentSetoid G ξ A := by
    intro S
    induction S using Finset.induction_on with
    | empty =>
      intro _
      rw [Finset.union_empty]
    | @insert e S _ ih =>
      intro hS
      have heR : e ∈ R := hS (Finset.mem_insert_self e S)
      have hSR : S ⊆ R := fun _ h => hS (Finset.mem_insert_of_mem h)
      have hendpoints : ∃ (u v : V) (huv : G.Adj u v),
          e = ⟨s(u, v), G.mem_edgeSet.mpr huv⟩ := by
        rcases e with ⟨e, heG⟩
        induction e using Sym2.inductionOn with
        | _ u v => exact ⟨u, v, G.mem_edgeSet.mp heG, rfl⟩
      rcases hendpoints with ⟨u, v, huv, rfl⟩
      rw [Finset.union_insert, componentSetoid_insert_eq_of_boundary ξ (A ∪ S) huv
        (hR u v huv heR)]
      exact ih hSR
  exact haux B.val B.property

theorem componentCount_union_removed [Finite V] (ξ : BoundaryCondition V)
    (R : Configuration G)
    (hR : ∀ (u v : V) (huv : G.Adj u v),
      (⟨s(u, v), G.mem_edgeSet.mpr huv⟩ : G.edgeSet) ∈ R → ξ.partition.r u v)
    (A : Configuration G) (B : RemovedConfiguration G R) :
    componentCount G ξ (A ∪ B.val) = componentCount G ξ A := by
  rw [componentCount, componentCount, componentSetoid_union_removed G ξ R hR A B]

/-- The FK weight with only edges outside `R` sampled. The component count is
still taken on all original vertices with the same boundary partition. -/
noncomputable def remainingWeight [Finite V] (q : Parameters)
    (ξ : BoundaryCondition V) (R : Configuration G) (A : RemainingConfiguration G R) : ℝ :=
  edgeParameter q ^ A.val.card *
    (1 - edgeParameter q) ^ (Nat.card G.edgeSet - R.card - A.val.card) *
    q.val ^ componentCount G ξ A.val

/-- The ordinary Bernoulli weight of the open subset of the removed edge set. -/
noncomputable def removedWeight (q : Parameters) (R : Configuration G)
    (B : RemovedConfiguration G R) : ℝ :=
  edgeParameter q ^ B.val.card * (1 - edgeParameter q) ^ (R.card - B.val.card)

omit [DecidableEq G.edgeSet] in
theorem remainingWeight_pos [Finite V] (q : Parameters) (ξ : BoundaryCondition V)
    (R : Configuration G) (A : RemainingConfiguration G R) :
    0 < remainingWeight G q ξ R A :=
  mul_pos
    (mul_pos (pow_pos (edgeParameter_pos q) _) (pow_pos (one_sub_edgeParameter_pos q) _))
    (pow_pos (clusterWeight_pos q) _)

omit [DecidableEq G.edgeSet] in
theorem removedWeight_pos (q : Parameters) (R : Configuration G)
    (B : RemovedConfiguration G R) : 0 < removedWeight G q R B :=
  mul_pos (pow_pos (edgeParameter_pos q) _) (pow_pos (one_sub_edgeParameter_pos q) _)

/-- The closed-edge exponents split without any truncated-subtraction artifact. -/
theorem closed_edge_count_split [Finite V] (R : Configuration G)
    (A : RemainingConfiguration G R) (B : RemovedConfiguration G R) :
    Nat.card G.edgeSet - (A.val.card + B.val.card) =
      (Nat.card G.edgeSet - R.card - A.val.card) + (R.card - B.val.card) := by
  have hA := remaining_card_add_removedSet_card_le G R A
  have hB := removed_card_le G R B
  omega

/-- The original FK weight factors into the remaining FK weight and the
independent Bernoulli weight on the prewired edges. -/
theorem weight_union_factorization [Finite V] (q : Parameters)
    (ξ : BoundaryCondition V) (R : Configuration G)
    (hR : ∀ (u v : V) (huv : G.Adj u v),
      (⟨s(u, v), G.mem_edgeSet.mpr huv⟩ : G.edgeSet) ∈ R → ξ.partition.r u v)
    (A : RemainingConfiguration G R) (B : RemovedConfiguration G R) :
    weight G q ξ (A.val ∪ B.val) = remainingWeight G q ξ R A * removedWeight G q R B := by
  rw [weight, remainingWeight, removedWeight,
    Finset.card_union_of_disjoint (remaining_disjoint_removed G R A B),
    componentCount_union_removed G ξ R hR A.val B,
    closed_edge_count_split G R A B, pow_add, pow_add]
  ring

end PottsDiscontinuity.FK
