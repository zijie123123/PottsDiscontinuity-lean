/- Adapted from an earlier, unpublished formalization of the planar FK model by the same author.
Parameter generalization: independent 0 < p < 1 and 1 ≤ q, with no upper bound on q. -/
module

public import PottsDiscontinuity.FK.DomainMarkov

/-!
# Exact decomposition over frozen edge states

The marginal of the original frozen edges and the induced conditional FK law
reconstruct the whole remaining-edge marginal. No independence of frozen and
remaining edges is asserted: the induced boundary partition depends on the
actually sampled frozen configuration.
-/

@[expose] public section

namespace PottsDiscontinuity.FK

open scoped BigOperators
noncomputable section

variable {V : Type*} [Finite V] {G : SimpleGraph V}
local instance disintegrationEdgeFintype : Fintype G.edgeSet := Fintype.ofFinite _
local instance disintegrationEdgeDecidableEq : DecidableEq G.edgeSet := Classical.decEq _
local instance disintegrationRemainingFintype (R : Configuration G) : Fintype (RemainingConfiguration G R) := Fintype.ofFinite _
local instance disintegrationRemovedFintype (R : Configuration G) : Fintype (RemovedConfiguration G R) := Fintype.ofFinite _

/-- The actual marginal of all original edges in the frozen set. -/
def frozenMarginalLaw (q : Parameters) (ξ : BoundaryCondition V) (R : Configuration G) :
    PMF (RemovedConfiguration G R) :=
  (law G q ξ).map (fun C => (configurationSplitEquiv G R C).2)

theorem frozenMarginalLaw_apply (q : Parameters) (ξ : BoundaryCondition V)
    (R : Configuration G) (H : RemovedConfiguration G R) :
    frozenMarginalLaw q ξ R H =
      ∑ A : RemainingConfiguration G R, law G q ξ (A.val ∪ H.val) := by
  classical
  have hsplit (B : RemainingConfiguration G R) (K : RemovedConfiguration G R) :
      configurationSplitEquiv G R (B.val ∪ K.val) = (B,K) :=
    (configurationSplitEquiv G R).apply_symm_apply (B,K)
  rw [frozenMarginalLaw, PMF.map_apply, tsum_fintype,
    ← (configurationSplitEquiv G R).symm.sum_comp, Fintype.sum_prod_type]
  simp only [configurationSplitEquiv_symm_apply, hsplit, Finset.sum_ite_eq,
    Finset.mem_univ, ite_true]

/-- The probability of the full configuration is its frozen-state marginal
times the exact induced conditional probability of all remaining edges. -/
theorem law_restore_eq_conditional_mul_marginal (q : Parameters)
    (ξ : BoundaryCondition V) (R : Configuration G)
    (H : RemovedConfiguration G R) (A : RemainingConfiguration G R) :
    law G q ξ (A.val ∪ H.val) =
      remainingLaw G q (frozenBoundary ξ H.val) R A * frozenMarginalLaw q ξ R H := by
  rw [frozenMarginalLaw_apply]
  simp only [law_apply, remainingLaw, FiniteProbability.pmf_apply]
  rw [← ENNReal.ofReal_sum_of_nonneg
    (fun B _ => (configurationProbability_pos G q ξ (B.val ∪ H.val)).le)]
  have hpos : 0 < ∑ B : RemainingConfiguration G R,
      configurationProbability G q ξ (B.val ∪ H.val) :=
    Finset.sum_pos (fun B _ => configurationProbability_pos G q ξ (B.val ∪ H.val))
      Finset.univ_nonempty
  have hr := (div_eq_iff hpos.ne').mp (configurationProbability_frozen_fiber_ratio q ξ R H A)
  change ENNReal.ofReal _ = ENNReal.ofReal (remainingWeight G q (frozenBoundary ξ H.val) R A /
    remainingPartitionFunction G q (frozenBoundary ξ H.val) R) * _
  rw [← ENNReal.ofReal_mul (div_pos (remainingWeight_pos G q (frozenBoundary ξ H.val) R A)
    (remainingPartitionFunction_pos G q (frozenBoundary ξ H.val) R)).le]
  exact congrArg ENNReal.ofReal hr

/-- The entire remaining-edge marginal is a mixture of the actual induced FK
laws, weighted by the true joint marginal of all frozen edges. -/
theorem law_map_remaining_eq_bind_frozen (q : Parameters) (ξ : BoundaryCondition V)
    (R : Configuration G) :
    (law G q ξ).map (fun C => (configurationSplitEquiv G R C).1) =
      (frozenMarginalLaw q ξ R).bind (fun H =>
        remainingLaw G q (frozenBoundary ξ H.val) R) := by
  classical
  ext A
  have hsplit (B : RemainingConfiguration G R) (K : RemovedConfiguration G R) :
      configurationSplitEquiv G R (B.val ∪ K.val) = (B,K) :=
    (configurationSplitEquiv G R).apply_symm_apply (B,K)
  rw [PMF.map_apply, tsum_fintype, ← (configurationSplitEquiv G R).symm.sum_comp,
    Fintype.sum_prod_type, Finset.sum_comm]
  simp only [configurationSplitEquiv_symm_apply, hsplit, Finset.sum_ite_eq,
    Finset.mem_univ, ite_true]
  rw [PMF.bind_apply, tsum_fintype]
  apply Finset.sum_congr rfl
  intro H hH
  rw [law_restore_eq_conditional_mul_marginal, mul_comm]

end
end PottsDiscontinuity.FK
