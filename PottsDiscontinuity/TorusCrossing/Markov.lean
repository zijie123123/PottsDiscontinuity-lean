module

public import PottsDiscontinuity.FK.ConditionalEmbeddedLaw
public import PottsDiscontinuity.FK.Events

/-!
# Domain Markov property and boundary comparison for an embedded subgraph

A conditioning of the FK measure of a graph `H` on the exact state of all edges outside an
embedded subgraph `G` gives, on `G`, the FK law with the pulled-back induced boundary condition.
We express this as an identity of probabilities of events, and combine it with boundary
comparison.
-/

@[expose] public section

namespace PottsDiscontinuity.TorusCrossing

open PottsDiscontinuity
open scoped Classical

theorem pmf_filter_toMeasure {X : Type*} [Fintype X] [MeasurableSpace X]
    [MeasurableSingletonClass X] (p : PMF X) (F : Set X) (h : ∃ a ∈ F, a ∈ p.support)
    (T : Set X) :
    (p.filter F h).toMeasure T = p.toMeasure (T ∩ F) / p.toMeasure F := by
  have hF : p.toMeasure F = ∑ x, F.indicator p x := PMF.toMeasure_apply_fintype _ _
  have hTF : p.toMeasure (T ∩ F) = ∑ x, (T ∩ F).indicator p x := PMF.toMeasure_apply_fintype _ _
  have hT : (p.filter F h).toMeasure T = ∑ x, T.indicator (p.filter F h) x :=
    PMF.toMeasure_apply_fintype _ _
  have hc : (∑' a', F.indicator p a') = ∑ x, F.indicator p x := tsum_fintype _
  rw [hT, hTF, hF, ENNReal.div_eq_inv_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  by_cases hxT : x ∈ T
  · rw [Set.indicator_of_mem hxT, PMF.filter_apply, hc]
    by_cases hxF : x ∈ F
    · rw [Set.indicator_of_mem (show x ∈ T ∩ F from ⟨hxT, hxF⟩)]
      simp only [Set.indicator_of_mem hxF, mul_comm]
    · rw [Set.indicator_of_notMem (show x ∉ T ∩ F from fun h => hxF h.2)]
      simp [Set.indicator_of_notMem hxF]
  · rw [Set.indicator_of_notMem hxT, Set.indicator_of_notMem (show x ∉ T ∩ F from fun h => hxT h.1)]
    simp

attribute [local instance] FK.configurationMeasurableSpace

/-- **Domain Markov for an embedded subgraph**, as an identity of probabilities. -/
theorem embedded_frozen_measure_eq {V W : Type*} [Finite V] [Finite W] (G : SimpleGraph V)
    (H : SimpleGraph W) (f : V ↪ W) (hGH : G.map f ≤ H) (q : FK.Parameters)
    (ξ : FK.BoundaryCondition W)
    (K : FK.RemovedConfiguration H (FK.subgraphRemovedEdges (G.map f) H))
    (S : Set (FK.Configuration G)) :
    FK.measure H q ξ ({C | FK.embeddedConfigurationRestriction G H f hGH C ∈ S} ∩
        FK.frozenStateEvent (FK.subgraphRemovedEdges (G.map f) H) K) =
      FK.measure G q (FK.isolatedExtensionPullbackBoundary f (FK.frozenBoundary ξ K.val)) S *
        FK.measure H q ξ (FK.frozenStateEvent (FK.subgraphRemovedEdges (G.map f) H) K) := by
  let : Fintype H.edgeSet := Fintype.ofFinite _
  let : Fintype G.edgeSet := Fintype.ofFinite _
  have hmain := FK.law_filter_frozen_map_embeddedRestriction G H f hGH q ξ K
  have hF := FK.frozenStateEvent_support q ξ (FK.subgraphRemovedEdges (G.map f) H) K
  have h1 : (FK.law G q (FK.isolatedExtensionPullbackBoundary f
      (FK.frozenBoundary ξ K.val))).toMeasure S =
      ((FK.law H q ξ).filter (FK.frozenStateEvent (FK.subgraphRemovedEdges (G.map f) H) K)
        hF).toMeasure
        ((FK.embeddedConfigurationRestriction G H f hGH) ⁻¹' S) := by
    rw [← hmain, PMF.toMeasure_map_apply _ _ _ measurable_from_top MeasurableSpace.measurableSet_top]
  rw [pmf_filter_toMeasure] at h1
  have hpos : 0 < FK.measure H q ξ
      (FK.frozenStateEvent (FK.subgraphRemovedEdges (G.map f) H) K) := by
    rw [FK.measure_pos_iff]
    obtain ⟨C, hC, _⟩ := hF
    exact ⟨C, hC⟩
  have hfin : FK.measure H q ξ (FK.frozenStateEvent (FK.subgraphRemovedEdges (G.map f) H) K) ≠ ⊤ :=
    MeasureTheory.measure_ne_top _ _
  change FK.measure H q ξ _ = (FK.law G q _).toMeasure S * FK.measure H q ξ _
  rw [h1]
  change _ = _ / FK.measure H q ξ _ * FK.measure H q ξ _
  rw [ENNReal.div_mul_cancel hpos.ne' hfin]
  rfl

end PottsDiscontinuity.TorusCrossing
