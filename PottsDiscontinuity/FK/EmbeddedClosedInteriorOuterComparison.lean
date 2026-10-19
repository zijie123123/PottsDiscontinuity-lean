/- Adapted from an earlier, unpublished formalization of the planar FK model by the same author.
Parameter generalization: independent 0 < p < 1 and 1 ≤ q, with no upper bound on q. -/
module

public import PottsDiscontinuity.FK.EmbeddedBoundaryUpper
public import PottsDiscontinuity.FK.EmbeddedClosedInteriorOuterBoundary

@[expose] public section

namespace PottsDiscontinuity.FK

noncomputable section

/-- The exact embedded restriction event in an increasing set has outer FK
probability bounded by the wired-interior FK probability when all frozen
exterior pullback partitions are dominated by wiring the interior. The graph
closure and boundary-avoidance premises are explicit; this statement does not
discharge them for any particular corridor. -/
theorem embeddedConfigurationRestriction_preimage_measure_le_wired_of_closedInterior
    {V W : Type*} [Finite V] [Finite W]
    {G : SimpleGraph V} {H : SimpleGraph W} (f : V ↪ W)
    (hGH : G.map f ≤ H) (q : Parameters) (ξ : BoundaryCondition W)
    (B : Set V)
    (hclosed : ∀ ⦃x : V⦄, x ∉ B → ∀ ⦃y : W⦄, H.Adj (f x) y →
      ∃ z : V, f z = y ∧ G.Adj x z)
    (hξavoid : ∀ ⦃x : V⦄, x ∉ B → f x ∉ ξ.boundary)
    (S : Set (Configuration G)) (hS : IsUpperSet S) :
    (measure H q ξ
      {A | embeddedConfigurationRestriction G H f hGH A ∈ S}).toReal ≤
      (measure G q (BoundaryCondition.wired B) S).toReal := by
  exact embeddedConfigurationRestriction_preimage_measure_le_of_frozen_partition
    G H f hGH q ξ (BoundaryCondition.wired B) S hS (by
      intro K
      exact isolatedExtensionPullback_frozenBoundary_partition_le_wired_of_closedInterior
        f hGH B hclosed ξ hξavoid K)

end
end PottsDiscontinuity.FK
