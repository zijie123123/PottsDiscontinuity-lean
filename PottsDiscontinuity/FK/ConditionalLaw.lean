/- Adapted from an earlier, unpublished formalization of the planar FK model by the same author.
Parameter generalization: independent 0 < p < 1 and 1 ≤ q, with no upper bound on q. -/
module

public import PottsDiscontinuity.FK.DomainMarkov

/-!
# The spatial Markov identity as actual PMF conditioning

The existing finite FK law is filtered on the event fixing every edge in R.
Its remaining-edge marginal is proved equal to the FK law with the induced
frozen-edge partition, using a full configuration-fiber calculation.
-/

@[expose] public section

namespace PottsDiscontinuity.FK

open scoped BigOperators
noncomputable section

variable {V : Type*} [Finite V] {G : SimpleGraph V}
local instance conditionalLawEdgeFintype : Fintype G.edgeSet := Fintype.ofFinite _
local instance conditionalLawEdgeDecidableEq : DecidableEq G.edgeSet := Classical.decEq _
local instance conditionalLawRemainingFintype (R : Configuration G) : Fintype (RemainingConfiguration G R) := Fintype.ofFinite _
local instance conditionalLawRemovedFintype (R : Configuration G) : Fintype (RemovedConfiguration G R) := Fintype.ofFinite _

omit [Finite V] in
private theorem restored_mem_frozen_iff (R : Configuration G)
    (H B : RemovedConfiguration G R) (A : RemainingConfiguration G R) :
    (A.val ∪ B.val) ∈ frozenStateEvent R H ↔ B = H := by
  change (A.val ∪ B.val) ∩ R = H.val ↔ B = H
  rw [Finset.union_inter_distrib_right, Finset.disjoint_iff_inter_eq_empty.mp A.property,
    Finset.empty_union, Finset.inter_eq_left.mpr B.property]
  exact Subtype.val_injective.eq_iff

/-- Every frozen configuration event has positive FK probability, since the
corresponding original configuration with no remaining open edges has positive mass. -/
theorem frozenStateEvent_support (q : Parameters) (ξ : BoundaryCondition V)
    (R : Configuration G) (H : RemovedConfiguration G R) :
    ∃ C ∈ frozenStateEvent R H, C ∈ (law G q ξ).support := by
  refine ⟨H.val, ?_, ?_⟩
  · exact Finset.inter_eq_left.mpr H.property
  · change law G q ξ H.val ≠ 0
    exact (law_pos G q ξ H.val).ne'

private theorem frozen_event_mass_sum (q : Parameters) (ξ : BoundaryCondition V)
    (R : Configuration G) (H : RemovedConfiguration G R) :
    (∑' C, (frozenStateEvent R H).indicator (law G q ξ) C) =
      ∑ A : RemainingConfiguration G R, law G q ξ (A.val ∪ H.val) := by
  classical
  rw [tsum_fintype, ← (configurationSplitEquiv G R).symm.sum_comp]
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro A hA
  simp only [configurationSplitEquiv_symm_apply, Set.indicator_apply,
    restored_mem_frozen_iff]
  simp

/-- Conditioning the full original law and retaining all remaining edges gives
the exact joint distribution, not just single-edge conditional marginals. -/
theorem law_filter_frozen_map_remaining (q : Parameters) (ξ : BoundaryCondition V)
    (R : Configuration G) (H : RemovedConfiguration G R) :
    ((law G q ξ).filter (frozenStateEvent R H) (frozenStateEvent_support q ξ R H)).map
        (fun C => (configurationSplitEquiv G R C).1) =
      remainingLaw G q (frozenBoundary ξ H.val) R := by
  classical
  rw [← frozenFiberLaw_eq_remainingLaw]
  ext A
  rw [PMF.map_apply, tsum_fintype, ← (configurationSplitEquiv G R).symm.sum_comp,
    Fintype.sum_prod_type]
  have hsplit (B : RemainingConfiguration G R) (K : RemovedConfiguration G R) :
      configurationSplitEquiv G R (B.val ∪ K.val) = (B,K) :=
    (configurationSplitEquiv G R).apply_symm_apply (B,K)
  simp_rw [PMF.filter_apply]
  rw [frozen_event_mass_sum]
  simp only [configurationSplitEquiv_symm_apply, hsplit,
    Set.indicator_apply, restored_mem_frozen_iff, ite_mul, zero_mul]
  rw [Finset.sum_comm]
  simp only [Finset.sum_ite_eq', Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  rw [frozenFiberLaw, FiniteProbability.pmf_apply]
  simp only [law_apply]
  rw [← ENNReal.ofReal_sum_of_nonneg
    (fun B _ => (configurationProbability_pos G q ξ (B.val ∪ H.val)).le)]
  have hpos : 0 < ∑ B : RemainingConfiguration G R,
      configurationProbability G q ξ (B.val ∪ H.val) :=
    Finset.sum_pos (fun B _ => configurationProbability_pos G q ξ (B.val ∪ H.val))
      Finset.univ_nonempty
  rw [FiniteProbability.partition, ENNReal.ofReal_div_of_pos hpos]
  rfl

end
end PottsDiscontinuity.FK
