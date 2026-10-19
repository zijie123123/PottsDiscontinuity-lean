/- Adapted from an earlier, unpublished formalization of the planar FK model by the same author.
Parameter generalization: independent 0 < p < 1 and 1 ≤ q, with no upper bound on q. -/
module

public import PottsDiscontinuity.FK.BoundaryComparison
public import PottsDiscontinuity.FK.EdgeRestriction

/-!
# FKG and boundary comparison for the actual remaining-edge law

The exact configuration order isomorphism transports the complete finite FK
inequalities from the same-vertex deleted graph. The edge set R is arbitrary;
no prewiring, conditional independence, or comparison premise is added.
-/

@[expose] public section

namespace PottsDiscontinuity.FK

open scoped BigOperators
noncomputable section

variable {V : Type*} [Finite V] (G : SimpleGraph V)

local instance remainingComparisonEdgeFintype : Fintype G.edgeSet := Fintype.ofFinite _
local instance remainingComparisonDeletedEdgeFintype (R : Configuration G) :
    Fintype (edgeRestriction G R).edgeSet := Fintype.ofFinite _
local instance remainingComparisonConfigurationFintype (R : Configuration G) :
    Fintype (RemainingConfiguration G R) := Fintype.ofFinite _

/-- Exact matching point masses under the proved configuration bijection. -/
theorem remainingLaw_apply_edgeRestriction (q : Parameters) (ξ : BoundaryCondition V)
    (R : Configuration G) (A : Configuration (edgeRestriction G R)) :
    remainingLaw G q ξ R (edgeRestrictionConfigurationEquiv G R A) =
      law (edgeRestriction G R) q ξ A := by
  rw [← law_edgeRestriction_map, FiniteProbability.map_equiv_apply, Equiv.symm_apply_apply]

/-- Reindexing any real observable gives its actual expectation on the deleted graph. -/
theorem remainingLaw_sum_toReal (q : Parameters) (ξ : BoundaryCondition V)
    (R : Configuration G) (f : RemainingConfiguration G R → ℝ) :
    (∑ A, (remainingLaw G q ξ R A).toReal * f A) =
      ∑ C, configurationProbability (edgeRestriction G R) q ξ C *
        f (edgeRestrictionConfigurationEquiv G R C) := by
  rw [← (edgeRestrictionConfigurationEquiv G R).sum_comp
    (fun A => (remainingLaw G q ξ R A).toReal * f A)]
  apply Finset.sum_congr rfl
  intro C hC
  rw [remainingLaw_apply_edgeRestriction, law_apply,
    ENNReal.toReal_ofReal (configurationProbability_pos _ _ _ _).le]

/-- Coarser boundary identifications increase every nonnegative increasing
observable of all actually sampled remaining edges. -/
theorem remainingLaw_boundary_comparison (q : Parameters) (ξ η : BoundaryCondition V)
    (hξη : ξ.partition ≤ η.partition) (R : Configuration G)
    (f : RemainingConfiguration G R → ℝ) (hf0 : ∀ A, 0 ≤ f A) (hf : Monotone f) :
    (∑ A, (remainingLaw G q ξ R A).toReal * f A) ≤
      ∑ A, (remainingLaw G q η R A).toReal * f A := by
  rw [remainingLaw_sum_toReal, remainingLaw_sum_toReal]
  have hmono : Monotone (fun C => f (edgeRestrictionConfigurationEquiv G R C)) :=
    hf.comp (edgeRestrictionConfigurationOrderIso G R).monotone
  simpa only [mul_comm] using configurationProbability_boundary_comparison
    (G := edgeRestriction G R) q ξ η hξη
    (fun C => f (edgeRestrictionConfigurationEquiv G R C))
    (fun C => hf0 _) hmono

/-- Nonnegative increasing observables are positively associated under the
existing normalized remaining-edge PMF. -/
theorem remainingLaw_positive_association (q : Parameters) (ξ : BoundaryCondition V)
    (R : Configuration G) (f g : RemainingConfiguration G R → ℝ)
    (hf0 : ∀ A, 0 ≤ f A) (hg0 : ∀ A, 0 ≤ g A) (hf : Monotone f) (hg : Monotone g) :
    (∑ A, (remainingLaw G q ξ R A).toReal * f A) *
      (∑ A, (remainingLaw G q ξ R A).toReal * g A) ≤
        ∑ A, (remainingLaw G q ξ R A).toReal * (f A * g A) := by
  simp only [remainingLaw_sum_toReal]
  exact configurationProbability_positive_association (G := edgeRestriction G R) q ξ
    (fun C => f (edgeRestrictionConfigurationEquiv G R C))
    (fun C => g (edgeRestrictionConfigurationEquiv G R C))
    (fun C => hf0 _) (fun C => hg0 _)
    (hf.comp (edgeRestrictionConfigurationOrderIso G R).monotone)
    (hg.comp (edgeRestrictionConfigurationOrderIso G R).monotone)

/-- Every subset of the finite remaining-configuration carrier is measurable. -/
abbrev remainingConfigurationMeasurableSpace (R : Configuration G) :
    MeasurableSpace (RemainingConfiguration G R) := ⊤

attribute [local instance] remainingConfigurationMeasurableSpace

local instance remainingComparisonDiscrete (R : Configuration G) :
    DiscreteMeasurableSpace (RemainingConfiguration G R) :=
  ⟨fun _ => MeasurableSpace.measurableSet_top⟩

/-- The genuine probability measure induced by the existing remaining-edge PMF
on the full power-set sigma algebra. -/
def remainingMeasure (q : Parameters) (ξ : BoundaryCondition V) (R : Configuration G) :
    MeasureTheory.Measure (RemainingConfiguration G R) := (remainingLaw G q ξ R).toMeasure

instance remainingMeasure_isProbabilityMeasure (q : Parameters)
    (ξ : BoundaryCondition V) (R : Configuration G) :
    MeasureTheory.IsProbabilityMeasure (remainingMeasure G q ξ R) :=
  PMF.toMeasure.isProbabilityMeasure _

end
end PottsDiscontinuity.FK
