/- Adapted from an earlier, unpublished formalization of the planar FK model by the same author.
Parameter generalization: independent 0 < p < 1 and 1 ≤ q, with no upper bound on q. -/
module

public import PottsDiscontinuity.FK.Parameters
public import PottsDiscontinuity.FK.Graph
public import PottsDiscontinuity.FK.Probability
public import Mathlib.Data.Fintype.Powerset

/-!
# The finite random-cluster probability law

Equation (1.2) of the source paper, including every isolated vertex in the
boundary-wired component count. The open configuration contains only original
edges of `G`; the boundary partition modifies the weight, not actual paths.
-/

@[expose] public section

namespace PottsDiscontinuity.FK

open scoped BigOperators

noncomputable section

variable {V : Type*} [Finite V] (G : SimpleGraph V)

local instance edgeFintype : Fintype G.edgeSet := Fintype.ofFinite G.edgeSet

/-- The numerator in the finite FK law (1.2). -/
def weight (q : Parameters) (ξ : BoundaryCondition V) (A : Configuration G) : ℝ :=
  edgeParameter q ^ A.card *
    (1 - edgeParameter q) ^ (Nat.card G.edgeSet - A.card) *
    q.val ^ componentCount G ξ A

theorem weight_pos (q : Parameters) (ξ : BoundaryCondition V) (A : Configuration G) :
    0 < weight G q ξ A :=
  mul_pos
    (mul_pos (pow_pos (edgeParameter_pos q) _) (pow_pos (one_sub_edgeParameter_pos q) _))
    (pow_pos (clusterWeight_pos q) _)

/-- The finite partition function from equation (1.2). -/
def partitionFunction (q : Parameters) (ξ : BoundaryCondition V) : ℝ :=
  FiniteProbability.partition (weight G q ξ)

theorem partitionFunction_pos (q : Parameters) (ξ : BoundaryCondition V) :
    0 < partitionFunction G q ξ :=
  FiniteProbability.partition_pos (weight G q ξ) (weight_pos G q ξ)

/-- The real probability of a single edge configuration in the finite FK law. -/
def configurationProbability (q : Parameters) (ξ : BoundaryCondition V)
    (A : Configuration G) : ℝ :=
  weight G q ξ A / partitionFunction G q ξ

theorem configurationProbability_pos (q : Parameters) (ξ : BoundaryCondition V)
    (A : Configuration G) : 0 < configurationProbability G q ξ A :=
  div_pos (weight_pos G q ξ A) (partitionFunction_pos G q ξ)

theorem sum_configurationProbability (q : Parameters) (ξ : BoundaryCondition V) :
    ∑ A : Configuration G, configurationProbability G q ξ A = 1 :=
  FiniteProbability.sum_probability (weight G q ξ) (weight_pos G q ξ)

/-- The finite FK law as a genuine probability mass function. -/
def law (q : Parameters) (ξ : BoundaryCondition V) : PMF (Configuration G) :=
  FiniteProbability.pmf (weight G q ξ) (weight_pos G q ξ)

theorem law_apply (q : Parameters) (ξ : BoundaryCondition V) (A : Configuration G) :
    law G q ξ A = ENNReal.ofReal (configurationProbability G q ξ A) := rfl

theorem law_pos (q : Parameters) (ξ : BoundaryCondition V) (A : Configuration G) :
    0 < law G q ξ A :=
  FiniteProbability.pmf_pos (weight G q ξ) (weight_pos G q ξ) A

/-- Every subset of the finite configuration space is measurable. -/
abbrev configurationMeasurableSpace : MeasurableSpace (Configuration G) := ⊤

attribute [local instance] configurationMeasurableSpace

local instance modelConfigurationDiscreteMeasurable : DiscreteMeasurableSpace (Configuration G) :=
  ⟨fun _ => MeasurableSpace.measurableSet_top⟩

/-- The measure on the full power-set sigma algebra of finite configurations. -/
def measure (q : Parameters) (ξ : BoundaryCondition V) :
    MeasureTheory.Measure (Configuration G) :=
  (law G q ξ).toMeasure

instance measure_isProbabilityMeasure (q : Parameters) (ξ : BoundaryCondition V) :
    MeasureTheory.IsProbabilityMeasure (measure G q ξ) :=
  PMF.toMeasure.isProbabilityMeasure _

/-- An arbitrary finite FK event has exactly the sum of its configuration masses. -/
theorem measure_apply (q : Parameters) (ξ : BoundaryCondition V)
    (s : Set (Configuration G)) :
    measure G q ξ s = ∑ A, s.indicator (law G q ξ) A :=
  PMF.toMeasure_apply_fintype _ _

end

end PottsDiscontinuity.FK
