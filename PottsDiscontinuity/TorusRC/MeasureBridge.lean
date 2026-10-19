module

public import PottsDiscontinuity.FK.ProbabilityProduct
public import PottsDiscontinuity.TorusLoops.RectangleLaw
public import PottsDiscontinuity.TorusRC.IndexedGraphBridge

/-! # The large-period torus law as an ordinary finite FK law -/

@[expose] public section

namespace PottsDiscontinuity.TorusRC

open MeasureTheory Torus

attribute [local instance] FK.configurationMeasurableSpace

variable {N M : ℕ}

noncomputable section

local instance torusBridgeEdgeFintype (hN : Even N) (hM : Even M) :
    Fintype (fullDiamondGraph hN hM).edgeSet := Fintype.ofFinite _

/-- The free FK parameters corresponding to the critical torus parameter. -/
def torusRCBridgeParameters (q : Set.Ici (1 : ℝ)) : FK.Parameters :=
  torusRCFKParameters q

/-- Reindexing the torus PMF by the unique indexed-edge/simple-edge
equivalence gives the free finite FK PMF on the diamond torus. -/
theorem torusRCPMF_map_edgeEquiv (hN : Even N) (hM : Even M)
    (hN4 : 4 ≤ N) (hM4 : 4 ≤ M) (q : Set.Ici (1 : ℝ)) :
    (torusRCPMF hN hM q).map (torusRCConfigurationEquiv hN hM hN4 hM4) =
      FK.law (fullDiamondGraph hN hM) (torusRCBridgeParameters q)
        (FK.BoundaryCondition.free ∅) := by
  classical
  exact FK.FiniteProbability.pmf_map_equiv_of_weight_eq
    (e := torusRCConfigurationEquiv hN hM hN4 hM4)
    (w := torusRCWeight hN hM q)
    (v := FK.weight (fullDiamondGraph hN hM) (torusRCBridgeParameters q)
      (FK.BoundaryCondition.free ∅))
    (hw := torusRCWeight_pos hN hM q)
    (hv := FK.weight_pos (fullDiamondGraph hN hM) (torusRCBridgeParameters q)
      (FK.BoundaryCondition.free ∅))
    (h := fun A => torusRCWeight_eq_fk_weight hN hM hN4 hM4 q A)

/-- The indexed and graph partition functions agree under the edge bijection. -/
theorem torusRCPartition_eq_fk (hN : Even N) (hM : Even M)
    (hN4 : 4 ≤ N) (hM4 : 4 ≤ M) (q : Set.Ici (1 : ℝ)) :
    torusRCPartition hN hM q =
      FK.partitionFunction (fullDiamondGraph hN hM) (torusRCBridgeParameters q)
        (FK.BoundaryCondition.free ∅) := by
  classical
  let e := torusRCConfigurationEquiv hN hM hN4 hM4
  unfold torusRCPartition FK.partitionFunction FK.FiniteProbability.partition
  calc
    (∑ A, torusRCWeight hN hM q A) =
        ∑ A, FK.weight (fullDiamondGraph hN hM) (torusRCBridgeParameters q)
          (FK.BoundaryCondition.free ∅) (e A) := by
            apply Finset.sum_congr rfl
            intro A _
            exact torusRCWeight_eq_fk_weight hN hM hN4 hM4 q A
    _ = ∑ C, FK.weight (fullDiamondGraph hN hM) (torusRCBridgeParameters q)
          (FK.BoundaryCondition.free ∅) C := e.sum_comp _

/-- Every indexed configuration mass is the free FK configuration mass after
the unique edge reindexing. -/
theorem torusRCMass_eq_fk_configurationProbability (hN : Even N) (hM : Even M)
    (hN4 : 4 ≤ N) (hM4 : 4 ≤ M) (q : Set.Ici (1 : ℝ))
    (A : RCConfig N M) :
    torusRCMass hN hM q A =
      FK.configurationProbability (fullDiamondGraph hN hM) (torusRCBridgeParameters q)
        (FK.BoundaryCondition.free ∅)
        (torusRCConfigurationEquiv hN hM hN4 hM4 A) := by
  rw [torusRCMass, FK.configurationProbability,
    torusRCWeight_eq_fk_weight hN hM hN4 hM4 q A,
    torusRCPartition_eq_fk hN hM hN4 hM4 q]
  rfl

/-- The torus probability measure is the image of the periodic free-boundary
FK measure under the edge-indexing equivalence. -/
theorem torusRCMeasure_map_edgeEquiv (hN : Even N) (hM : Even M)
    (hN4 : 4 ≤ N) (hM4 : 4 ≤ M) (q : Set.Ici (1 : ℝ)) :
    Measure.map (torusRCConfigurationEquiv hN hM hN4 hM4)
        (torusRCMeasure hN hM q) =
      FK.measure (fullDiamondGraph hN hM) (torusRCBridgeParameters q)
        (FK.BoundaryCondition.free ∅) := by
  have hpmf := torusRCPMF_map_edgeEquiv hN hM hN4 hM4 q
  have hmeasure := congrArg
    (fun p : PMF (FK.Configuration (fullDiamondGraph hN hM)) =>
      @PMF.toMeasure _ (FK.configurationMeasurableSpace (fullDiamondGraph hN hM)) p) hpmf
  rw [← PMF.toMeasure_map _ _ (Measurable.of_discrete)] at hmeasure
  simpa [torusRCMeasure, FK.measure] using hmeasure

/-- Event probabilities transport exactly through the indexed-edge equivalence. -/
theorem torusRCProbability_eq_fk_image (hN : Even N) (hM : Even M)
    (hN4 : 4 ≤ N) (hM4 : 4 ≤ M) (q : Set.Ici (1 : ℝ))
    (E : Set (RCConfig N M)) :
    torusRCProbability hN hM q E =
      (FK.measure (fullDiamondGraph hN hM) (torusRCBridgeParameters q)
        (FK.BoundaryCondition.free ∅)).real
        (torusRCConfigurationEquiv hN hM hN4 hM4 '' E) := by
  rw [← torusRCMeasure_map_edgeEquiv hN hM hN4 hM4 q]
  unfold torusRCProbability Measure.real
  rw [Measure.map_apply (Measurable.of_discrete) MeasurableSpace.measurableSet_top]
  simp only [Set.preimage_image_eq _ (torusRCConfigurationEquiv hN hM hN4 hM4).injective]

end

end PottsDiscontinuity.TorusRC
