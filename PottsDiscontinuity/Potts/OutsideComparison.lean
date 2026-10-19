module

public import PottsDiscontinuity.FK.ConditionalEmbeddedBoundaryUpper
public import PottsDiscontinuity.FK.EmbeddedClosedInteriorOuterBoundary
public import PottsDiscontinuity.FK.Events
public import PottsDiscontinuity.Potts.FiniteConditioning
public import PottsDiscontinuity.Potts.FiniteEnergyBounds

/-! Domain-Markov comparison retaining an arbitrary event on exterior edges. -/

@[expose] public section

namespace PottsDiscontinuity.Potts

open MeasureTheory Classical
noncomputable section

variable {V W : Type*} [Finite V] [Finite W]
    (G : SimpleGraph V) (H : SimpleGraph W) (f : V ↪ W) (hGH : G.map f ≤ H)
attribute [local instance] FK.configurationMeasurableSpace
local instance outsideEdgeFintype : Fintype H.edgeSet := Fintype.ofFinite _
local instance outsideEdgeDecidable : DecidableEq H.edgeSet := Classical.decEq _
local instance outsideRemovedFintype (R : FK.Configuration H) :
    Fintype (FK.RemovedConfiguration H R) := Fintype.ofFinite _

/-- The joint probability of an increasing inner event and any outside event
is at most the wired-inner probability times the outside probability. -/
theorem embedded_joint_outside_le (q : FK.Parameters) (ξ : FK.BoundaryCondition W)
    (η : FK.BoundaryCondition V)
    (hpart : ∀ K : FK.RemovedConfiguration H (FK.subgraphRemovedEdges (G.map f) H),
      (FK.isolatedExtensionPullbackBoundary f (FK.frozenBoundary ξ K.val)).partition ≤
        η.partition)
    (S : Set (FK.Configuration G)) (hS : IsUpperSet S)
    (T : Set (FK.RemovedConfiguration H (FK.subgraphRemovedEdges (G.map f) H))) :
    (FK.measure H q ξ {C | FK.embeddedConfigurationRestriction G H f hGH C ∈ S ∧
      (FK.configurationSplitEquiv H (FK.subgraphRemovedEdges (G.map f) H) C).2 ∈ T}).toReal ≤
    (FK.measure G q η S).toReal *
      (FK.measure H q ξ {C |
        (FK.configurationSplitEquiv H (FK.subgraphRemovedEdges (G.map f) H) C).2 ∈ T}).toReal := by
  let R := FK.subgraphRemovedEdges (G.map f) H
  let r := fun C => (FK.configurationSplitEquiv H R C).2
  let U : Set (FK.Configuration H) :=
    {C | FK.embeddedConfigurationRestriction G H f hGH C ∈ S}
  have hfiber (K : FK.RemovedConfiguration H R) :
      {C | r C = K} = FK.frozenStateEvent R K := by
    ext C
    exact Subtype.ext_iff
  have hbound (K : FK.RemovedConfiguration H R) :
      (FK.measure H q ξ (U ∩ {C | r C = K})).toReal ≤
      (FK.measure G q η S).toReal * (FK.measure H q ξ {C | r C = K}).toReal := by
    have hcond := FK.filteredConditionalEmbeddedEvent_measure_le_boundary
      G H f hGH q ξ K η (hpart K) S hS
    rw [PMF.toMeasure_map_apply _ _ _ (measurable_from_top) (MeasurableSpace.measurableSet_top)] at hcond
    change ((FK.law H q ξ).filter (FK.frozenStateEvent R K)
      (FK.frozenStateEvent_support q ξ R K)).toMeasure.real U ≤ _ at hcond
    rw [finite_filter_measureReal] at hcond
    have hpos : 0 < (FK.measure H q ξ (FK.frozenStateEvent R K)).toReal := by
      apply ENNReal.toReal_pos
      · exact ((FK.measure_pos_iff H q ξ (FK.frozenStateEvent R K)).mpr
          ⟨K.val, Finset.inter_eq_left.mpr K.property⟩).ne'
      · exact measure_ne_top _ _
    rw [hfiber]
    exact (div_le_iff₀ hpos).mp hcond
  change (FK.law H q ξ).toMeasure.real {C | C ∈ U ∧ r C ∈ T} ≤
    (FK.measure G q η S).toReal * (FK.law H q ξ).toMeasure.real {C | r C ∈ T}
  rw [finite_measure_fibers]
  have hm := finite_measure_fibers (FK.law H q ξ) r Set.univ T
  simp only [Set.mem_univ, true_and, Set.univ_inter] at hm
  rw [hm, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro K _
  by_cases hK : K ∈ T
  · simp only [hK, ite_true]
    exact hbound K
  · simp [hK]

/-- Exterior closed-edge corrections retain the wired-interior upper bound,
even after selecting the complement of the correction event. -/
theorem embedded_joint_not_allClosed_le (q : FK.Parameters) (ξ : FK.BoundaryCondition W)
    (B : Set V)
    (hclosed : ∀ ⦃x : V⦄, x ∉ B → ∀ ⦃y : W⦄, H.Adj (f x) y →
      ∃ z : V, f z = y ∧ G.Adj x z)
    (hξavoid : ∀ ⦃x : V⦄, x ∉ B → f x ∉ ξ.boundary)
    (F : Finset H.edgeSet) (hF : F ⊆ FK.subgraphRemovedEdges (G.map f) H)
    (S : Set (FK.Configuration G)) (hS : IsUpperSet S) :
    (FK.measure H q ξ ({C | FK.embeddedConfigurationRestriction G H f hGH C ∈ S} ∩
      (allClosedEdges F)ᶜ)).toReal ≤
    (FK.measure G q (FK.BoundaryCondition.wired B) S).toReal *
      (1 - (FK.measure H q ξ (allClosedEdges F)).toReal) := by
  let R := FK.subgraphRemovedEdges (G.map f) H
  let T : Set (FK.RemovedConfiguration H R) := {K | ¬ Disjoint F K.val}
  have hdisj (C : FK.Configuration H) : Disjoint F (C ∩ R) ↔ Disjoint F C := by
    rw [Finset.disjoint_left, Finset.disjoint_left]
    constructor
    · intro h e he hc
      exact h he (Finset.mem_inter.mpr ⟨hc, hF he⟩)
    · intro h e he hc
      exact h he (Finset.mem_inter.mp hc).1
  have hcmp := embedded_joint_outside_le G H f hGH q ξ (FK.BoundaryCondition.wired B)
    (fun K => FK.isolatedExtensionPullback_frozenBoundary_partition_le_wired_of_closedInterior
      f hGH B hclosed ξ hξavoid K) S hS T
  have ht (C : FK.Configuration H) :
      (FK.configurationSplitEquiv H R C).2 ∈ T ↔ C ∈ (allClosedEdges F)ᶜ := by
    exact not_congr (hdisj C)
  have hevent : {C | (FK.configurationSplitEquiv H R C).2 ∈ T} =
      (allClosedEdges F)ᶜ := Set.ext ht
  have hjoint : {C | FK.embeddedConfigurationRestriction G H f hGH C ∈ S ∧
      (FK.configurationSplitEquiv H R C).2 ∈ T} =
      {C | FK.embeddedConfigurationRestriction G H f hGH C ∈ S} ∩ (allClosedEdges F)ᶜ := by
    ext C
    exact and_congr_right (fun _ => ht C)
  rw [hevent, hjoint] at hcmp
  have hc := measureReal_compl (μ := FK.measure H q ξ)
    (MeasurableSpace.measurableSet_top (s := allClosedEdges F))
  simp only [Measure.real, measure_univ, ENNReal.toReal_one] at hc
  rw [hc] at hcmp
  exact hcmp

end
end PottsDiscontinuity.Potts
