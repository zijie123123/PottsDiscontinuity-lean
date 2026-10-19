/- Adapted from an earlier, unpublished formalization of the planar FK model by the same author.
Parameter generalization: independent 0 < p < 1 and 1 ≤ q, with no upper bound on q. -/
module

public import PottsDiscontinuity.FK.Marginal

/-!
# Wiring induced by a frozen subset of original edges

The induced partition is exactly original wiring joined with connectivity in
the actually open frozen edges. It is a partition on all original vertices;
its support is allowed to be the whole vertex carrier. This does not add any
actual open paths to the remaining-edge configuration. The component relation
and full FK weights agree with the original model after the frozen edges are
restored. Conditional normalization is proved separately.
-/

@[expose] public section

namespace PottsDiscontinuity.FK

variable {V : Type*} {G : SimpleGraph V}

/-- Identifications induced by the original boundary and the frozen open edges. -/
def frozenBoundary (ξ : BoundaryCondition V) (H : Configuration G) : BoundaryCondition V where
  boundary := Set.univ
  partition := componentSetoid G ξ H
  supported := fun _ => Or.inr ⟨Set.mem_univ _, Set.mem_univ _⟩

section
variable [DecidableEq G.edgeSet]

/-- Exactly the same components result from retaining the frozen edges or
incorporating their actual connections into the partition. -/
theorem componentSetoid_union_frozen (ξ : BoundaryCondition V) (A H : Configuration G) :
    componentSetoid G ξ (A ∪ H) = componentSetoid G (frozenBoundary ξ H) A := by
  apply le_antisymm
  · apply componentSetoid_le
    · apply reachableSetoid_le_of_adj
      intro x y hxy
      rw [openGraph_adj] at hxy
      rcases hxy with ⟨e, he, hexy⟩
      rcases Finset.mem_union.mp he with he | he
      · apply actualConnected_component
        apply actualConnected_of_adj
        rw [openGraph_adj]
        exact ⟨e,he,hexy⟩
      · apply boundary_component
        apply actualConnected_component
        apply actualConnected_of_adj
        rw [openGraph_adj]
        exact ⟨e,he,hexy⟩
    · intro x y hxy
      exact boundary_component G (frozenBoundary ξ H) A (boundary_component G ξ H hxy)
  · apply componentSetoid_le
    · intro x y hxy
      exact actualConnected_component G ξ (A ∪ H)
        (actualConnected_mono Finset.subset_union_left hxy)
    · exact componentSetoid_mono ξ Finset.subset_union_right

theorem componentCount_union_frozen [Finite V] (ξ : BoundaryCondition V)
    (A H : Configuration G) :
    componentCount G ξ (A ∪ H) = componentCount G (frozenBoundary ξ H) A := by
  rw [componentCount, componentCount, componentSetoid_union_frozen]

/-- No prewiring assumption on R is needed: freezing its state induces the
correct actual partition. Every original vertex remains in the component count. -/
theorem weight_union_frozen_factorization [Finite V] (q : Parameters)
    (ξ : BoundaryCondition V) (R : Configuration G)
    (A : RemainingConfiguration G R) (H : RemovedConfiguration G R) :
    weight G q ξ (A.val ∪ H.val) =
      remainingWeight G q (frozenBoundary ξ H.val) R A * removedWeight G q R H := by
  rw [weight, remainingWeight, removedWeight,
    Finset.card_union_of_disjoint (remaining_disjoint_removed G R A H),
    componentCount_union_frozen,
    closed_edge_count_split G R A H, pow_add, pow_add]
  ring

end

noncomputable section

open scoped BigOperators

variable [Finite V]
local instance domainMarkovEdgeFintype : Fintype G.edgeSet := Fintype.ofFinite _
local instance domainMarkovEdgeDecidableEq : DecidableEq G.edgeSet := Classical.decEq _
local instance domainMarkovRemainingFintype (R : Configuration G) : Fintype (RemainingConfiguration G R) := Fintype.ofFinite _

/-- The exact normalized probability of a remaining configuration in the fiber
where every edge of R has the specified state H. The denominator sums every
configuration in that fiber, not only single-edge marginals. -/
theorem configurationProbability_frozen_fiber_ratio (q : Parameters)
    (ξ : BoundaryCondition V) (R : Configuration G)
    (H : RemovedConfiguration G R) (A : RemainingConfiguration G R) :
    configurationProbability G q ξ (A.val ∪ H.val) /
      (∑ B : RemainingConfiguration G R, configurationProbability G q ξ (B.val ∪ H.val)) =
    remainingWeight G q (frozenBoundary ξ H.val) R A /
      remainingPartitionFunction G q (frozenBoundary ξ H.val) R := by
  simp_rw [configurationProbability, weight_union_frozen_factorization]
  rw [← Finset.sum_div, ← Finset.sum_mul]
  change (_ * removedWeight G q R H / partitionFunction G q ξ) /
    (remainingPartitionFunction G q (frozenBoundary ξ H.val) R *
      removedWeight G q R H / partitionFunction G q ξ) = _
  field_simp [(partitionFunction_pos G q ξ).ne',
    (remainingPartitionFunction_pos G q (frozenBoundary ξ H.val) R).ne',
    (removedWeight_pos G q R H).ne']

/-- A PMF obtained by normalizing the original probabilities on the exact frozen
configuration fiber. No Markov property is placed in this definition. -/
def frozenFiberLaw (q : Parameters) (ξ : BoundaryCondition V)
    (R : Configuration G) (H : RemovedConfiguration G R) :
    PMF (RemainingConfiguration G R) :=
  FiniteProbability.pmf (fun A => configurationProbability G q ξ (A.val ∪ H.val))
    (fun A => configurationProbability_pos G q ξ (A.val ∪ H.val))

/-- The entire normalized fiber law is the remaining-edge FK law with the
partition induced by the actual frozen open paths and original boundary wiring. -/
theorem frozenFiberLaw_eq_remainingLaw (q : Parameters) (ξ : BoundaryCondition V)
    (R : Configuration G) (H : RemovedConfiguration G R) :
    frozenFiberLaw q ξ R H = remainingLaw G q (frozenBoundary ξ H.val) R := by
  ext A
  rw [frozenFiberLaw, FiniteProbability.pmf_apply]
  change ENNReal.ofReal (_ / ∑ B : RemainingConfiguration G R,
    configurationProbability G q ξ (B.val ∪ H.val)) = _
  rw [configurationProbability_frozen_fiber_ratio]
  rfl

/-- The actual event fixing every sampled edge of R, both its open and closed states. -/
def frozenStateEvent (R : Configuration G) (H : RemovedConfiguration G R) :
    Set (Configuration G) := {C | C ∩ R = H.val}

end
end PottsDiscontinuity.FK
