module

public import PottsDiscontinuity.TorusLoops.RectangleClusterBoundary
public import PottsDiscontinuity.TorusLoops.RectangleRootCrossings

/-!
# One-step bound for exploration outside a revealed cluster

Freezing all edges not in the induced complement graph, when the frozen open
edges lie within the explored region, leaves a free FK boundary on the
complement. An increasing crossing in that complement is bounded by the
whole-rectangle rooted crossing, hence by the free one-arm probability.
-/

@[expose] public section

namespace PottsDiscontinuity.TorusLoops

open MeasureTheory
open PottsDiscontinuity.Torus
open PottsDiscontinuity.CorrLength
open PottsDiscontinuity.Zhang
open PottsDiscontinuity.FK

noncomputable section

local instance explorationGenericEdgeFintype
    {V : Type*} [Finite V] {G : SimpleGraph V} : Fintype G.edgeSet :=
  Fintype.ofFinite _

local instance explorationGenericEdgeDecidableEq
    {V : Type*} [Finite V] {G : SimpleGraph V} : DecidableEq G.edgeSet :=
  Classical.decEq _

variable {N M : ℕ}

/-- Vertices in the complement of an explored set of rectangle vertices. -/
abbrev RectangleComplementVertex (N M : ℕ) (U : Set (FaceVertex N M true)) :=
  {x : FaceVertex N M true // x ∉ U}

/-- The subgraph induced by the vertices outside the explored region. -/
def rectangleComplementGraph (hN : Even N) (hM : Even M)
    (U : Set (FaceVertex N M true)) : SimpleGraph (RectangleComplementVertex N M U) :=
  (rectangleBaseGraph hN hM).induce {x | x ∉ U}

/-- The natural inclusion of the unexplored vertices in the rectangle. -/
def rectangleComplementEmbedding (U : Set (FaceVertex N M true)) :
    RectangleComplementVertex N M U ↪ FaceVertex N M true :=
  Function.Embedding.subtype _

theorem rectangleComplementGraph_map_le (hN : Even N) (hM : Even M)
    (U : Set (FaceVertex N M true)) :
    (rectangleComplementGraph hN hM U).map (rectangleComplementEmbedding U) ≤
      rectangleBaseGraph hN hM := by
  intro x y hxy
  rw [SimpleGraph.map_adj] at hxy
  rcases hxy with ⟨a, b, hab, rfl, rfl⟩
  exact (SimpleGraph.induce_adj).mp hab

/-- A rooted horizontal crossing event in the induced graph outside `U`. -/
def rectangleComplementRootCrossingEvent (hN : Even N) (hM : Even M)
    (U : Set (FaceVertex N M true)) (u : FaceVertex N M true) (huU : u ∉ U) :
    Set (Configuration (rectangleComplementGraph hN hM U)) :=
  {C | ∃ v : RectangleComplementVertex N M U,
    v.val.val.1.val + 1 = N ∧
    ActualConnected (rectangleComplementGraph hN hM U) C ⟨u, huU⟩ v}

private theorem rectangleComplementRootCrossingEvent_isUpperSet
    (hN : Even N) (hM : Even M) (U : Set (FaceVertex N M true))
    (u : FaceVertex N M true) (huU : u ∉ U) :
    IsUpperSet (rectangleComplementRootCrossingEvent hN hM U u huU) := by
  intro A B hAB hA
  rcases hA with ⟨v, hv, hconn⟩
  exact ⟨v, hv, actualConnected_mono hAB hconn⟩

private theorem actualConnected_embeddedConfigurationEmbedding
    {V W : Type*} (G : SimpleGraph V) (H : SimpleGraph W)
    (f : V ↪ W) (hGH : G.map f ≤ H)
    (A : Configuration G) (u v : V)
    (h : ActualConnected G A u v) :
    ActualConnected H (embeddedConfigurationEmbedding G H f hGH A) (f u) (f v) := by
  change (openGraph H
    (subgraphConfigurationEmbedding hGH (isolatedExtensionConfigurationEquiv G f A))).Reachable
      (f u) (f v)
  rw [openGraph_subgraphConfigurationEmbedding, openGraph_isolatedExtension]
  exact (reachable_isolatedExtension_apply (openGraph G A) f u v).2 h

private theorem fkLaw_measure_toReal_eq_expectation
    {V : Type*} [Finite V] {G : SimpleGraph V}
    (q : Parameters) (ξ : BoundaryCondition V)
    (S : Set (Configuration G)) :
    (measure G q ξ S).toReal =
      FiniteProbability.expectation (law G q ξ)
        (S.indicator (fun _ => (1 : ℝ))) := by
  rw [measure_toReal_eq_indicator_sum]
  unfold FiniteProbability.expectation
  apply Finset.sum_congr rfl
  intro A hA
  by_cases h : A ∈ S
  · simp [Set.indicator, h, law_apply,
      ENNReal.toReal_ofReal (configurationProbability_pos G q ξ A).le]
  · simp [Set.indicator, h]

private theorem rectangleFKEventProbability_eq_measure
    (hN : Even N) (hM : Even M) (q : Set.Ici (1 : ℝ))
    (E : Set (Configuration (rectangleBaseGraph hN hM))) :
    rectangleFKEventProbability hN hM q E =
      (measure (rectangleBaseGraph hN hM) (rectangleFKParameters q)
        (BoundaryCondition.free ∅) E).toReal := by
  rw [measure_toReal_eq_indicator_sum]
  unfold rectangleFKEventProbability rectangleFKEventWeight
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro C hC
  by_cases h : C ∈ E <;> simp [Set.indicator, h, configurationProbability,
    mul_comm]

/-- Conditional one-step exploration bound. The exact outside state `K` may
have arbitrary closed edges; its open edges must stay inside the explored set
`U`. The conditional law on the induced complement then has free boundary,
and the probability that the next left-boundary root crosses is at most the
free one-arm probability. -/
theorem rectangleConditionalRootCrossing_le_freeOneArm
    (hN : Even N) (hM : Even M) (q : Set.Ici (1 : ℝ))
    (U : Set (FaceVertex N M true)) (u : FaceVertex N M true)
    (hu : u.val.1.val = 0) (huU : u ∉ U)
    (K : RemovedConfiguration (rectangleBaseGraph hN hM)
      (subgraphRemovedEdges
        ((rectangleComplementGraph hN hM U).map (rectangleComplementEmbedding U))
        (rectangleBaseGraph hN hM)))
    (hK : ∀ ⦃x y : FaceVertex N M true⦄,
      (openGraph (rectangleBaseGraph hN hM) K.val).Adj x y → x ∈ U ∧ y ∈ U) :
    (PMF.toMeasure (((law (rectangleBaseGraph hN hM)
      (rectangleFKParameters q) (BoundaryCondition.free ∅)).filter
        (frozenStateEvent
          (subgraphRemovedEdges
            ((rectangleComplementGraph hN hM U).map (rectangleComplementEmbedding U))
            (rectangleBaseGraph hN hM)) K)
        (frozenStateEvent_support (rectangleFKParameters q)
          (BoundaryCondition.free ∅)
          (subgraphRemovedEdges
            ((rectangleComplementGraph hN hM U).map (rectangleComplementEmbedding U))
            (rectangleBaseGraph hN hM)) K)).map
        (embeddedConfigurationRestriction
          (rectangleComplementGraph hN hM U) (rectangleBaseGraph hN hM)
          (rectangleComplementEmbedding U)
          (rectangleComplementGraph_map_le hN hM U)))
      (rectangleComplementRootCrossingEvent hN hM U u huU)).toReal ≤
      (((Classical.choose (freeBoxLimit_existsUnique
        (rectangleFKParameters q))) (oneArmEvent (N / 2 - 1)) : NNReal) : ℝ) := by
  let G := rectangleBaseGraph hN hM
  let I := rectangleComplementGraph hN hM U
  let f := rectangleComplementEmbedding U
  let hIG := rectangleComplementGraph_map_le hN hM U
  let θ := rectangleFKParameters q
  let E := rectangleComplementRootCrossingEvent hN hM U u huU
  let T := rectangleRootCrossingEvent hN hM u
  let R := subgraphRemovedEdges (I.map f) G
  have hE : IsUpperSet E := by
    exact rectangleComplementRootCrossingEvent_isUpperSet hN hM U u huU
  have hpart :
      (isolatedExtensionPullbackBoundary f (frozenBoundary
        (BoundaryCondition.free ∅) K.val)).partition ≤
        (BoundaryCondition.free ∅).partition := by
    exact isolatedExtensionPullbackFrozenFree_of_openEdges_inside
      f hIG K U hK (fun x => x.property)
  have hconditional := filteredConditionalEmbeddedEvent_measure_le_boundary
    I G f hIG θ (BoundaryCondition.free ∅) K (BoundaryCondition.free ∅)
    hpart E hE
  have hTcontains (A : Configuration G) :
      embeddedConfigurationRestriction I G f hIG A ∈ E → A ∈ T := by
    intro hA
    rcases hA with ⟨v, hv, hconn⟩
    let D := embeddedConfigurationEmbedding I G f hIG
      (embeddedConfigurationRestriction I G f hIG A)
    have hDA : D ⊆ A := embeddedConfigurationEmbedding_restriction_subset I G f hIG A
    have hconnG : ActualConnected G D (f ⟨u, huU⟩) (f v) :=
      actualConnected_embeddedConfigurationEmbedding I G f hIG _ _ _ hconn
    have hconnA : ActualConnected G A (f ⟨u, huU⟩) (f v) :=
      actualConnected_mono hDA hconnG
    have hfu : f ⟨u, huU⟩ = u := rfl
    have hconnA' : ActualConnected G A u (f v) := by
      rw [← hfu]
      exact hconnA
    exact ⟨f v, hv, hconnA'⟩
  have hfreeCompare : (measure I θ (BoundaryCondition.free ∅) E).toReal ≤
      (measure G θ (BoundaryCondition.free ∅) T).toReal := by
    rw [fkLaw_measure_toReal_eq_expectation (G := I) θ (BoundaryCondition.free ∅) E,
      fkLaw_measure_toReal_eq_expectation (G := G) θ (BoundaryCondition.free ∅) T]
    let ind := E.indicator (fun _ => (1 : ℝ))
    have hind0 : ∀ A, 0 ≤ ind A := by
      intro A
      by_cases hA : A ∈ E <;> simp [ind, hA]
    have hind : Monotone ind := by
      intro A B hAB
      by_cases hA : A ∈ E
      · have hB := hE hAB hA
        simp [ind, hA, hB]
      · simp only [ind, Set.indicator_of_notMem hA]
        exact hind0 B
    have hcmp := embedded_free_marginal_comparison I G f hIG θ ∅ ∅ ind hind0 hind
    rw [FiniteProbability.expectation_map] at hcmp
    have hpoint (A : Configuration G) :
        ind (embeddedConfigurationRestriction I G f hIG A) ≤
          T.indicator (fun _ => (1 : ℝ)) A := by
      by_cases hA : embeddedConfigurationRestriction I G f hIG A ∈ E
      · have hTA := hTcontains A hA
        simp [ind, Set.indicator, hA, hTA]
      · by_cases hTA : A ∈ T <;> simp [ind, Set.indicator, hA, hTA]
    exact hcmp.trans (FiniteProbability.expectation_mono _ _ _ hpoint)
  have hroot : (measure G θ (BoundaryCondition.free ∅) T).toReal ≤
      (((Classical.choose (freeBoxLimit_existsUnique θ))
        (oneArmEvent (N / 2 - 1)) : NNReal) : ℝ) := by
    rw [← rectangleFKEventProbability_eq_measure hN hM q T]
    exact rectangleFKProbability_rootCrossing_le_freeOneArm hN hM u hu q
  simpa [G, I, f, hIG, θ, E, T, R] using hconditional.trans (hfreeCompare.trans hroot)

end
end PottsDiscontinuity.TorusLoops
