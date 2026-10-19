module

public import PottsDiscontinuity.Duality.DualConfigurationBridge
public import PottsDiscontinuity.Duality.RectangleDualAmbientMarginal
public import PottsDiscontinuity.Duality.WiredDomainComparison

/-! Exact duality on cylinders supported on true finite dual edges. -/

@[expose] public section

namespace PottsDiscontinuity.Duality

open FK FK.Medial MeasureTheory
noncomputable section

/-- The wired exterior class of the true dual is precisely the vertex boundary
of the expanded induced lattice domain, including the degenerate primal boxes. -/
lemma rectangleDualBoundary_eq_vertexBoundary (a : LatticeVertex) (w h : ℕ)
    (x : LatticeVertex) :
    x ∈ rectangleDualBoundary a w h ↔ x ∈ vertexBoundary (rectangleDualExpanded a w h) := by
  have hcoords (z : LatticeVertex) : z ∈ rectangleDualExpanded a w h ↔
      (a.1 - 1 ≤ z.1 ∧ z.1 ≤ a.1 + (w : ℤ)) ∧
      (a.2 - 1 ≤ z.2 ∧ z.2 ≤ a.2 + (h : ℤ)) := by
    simp only [rectangleDualExpanded, mem_latticeRectangle, Nat.cast_add, Nat.cast_one]
    omega
  constructor
  · intro hx
    obtain ⟨hxS, hxI⟩ := Finset.mem_filter.1 hx
    have hxcoord := (hcoords x).1 hxS
    have hside : x.1 = a.1 - 1 ∨ x.1 = a.1 + (w : ℤ) ∨
        x.2 = a.2 - 1 ∨ x.2 = a.2 + (h : ℤ) := by
      have hi : ¬ (a.1 ≤ x.1 ∧ x.1 < a.1 + (w : ℤ) ∧
          a.2 ≤ x.2 ∧ x.2 < a.2 + (h : ℤ)) := by
        intro hc
        exact hxI (Finset.mem_filter.mpr ⟨hxS, hc⟩)
      omega
    refine ⟨hxS, ?_⟩
    rcases hside with hx | hx | hx | hx
    · refine ⟨(x.1 - 1, x.2), ?_, ?_⟩
      · rw [squareLattice_adj_iff]; dsimp; omega
      · rw [hcoords]; dsimp; omega
    · refine ⟨(x.1 + 1, x.2), ?_, ?_⟩
      · rw [squareLattice_adj_iff]; dsimp; omega
      · rw [hcoords]; dsimp; omega
    · refine ⟨(x.1, x.2 - 1), ?_, ?_⟩
      · rw [squareLattice_adj_iff]; dsimp; omega
      · rw [hcoords]; dsimp; omega
    · refine ⟨(x.1, x.2 + 1), ?_, ?_⟩
      · rw [squareLattice_adj_iff]; dsimp; omega
      · rw [hcoords]; dsimp; omega
  · rintro ⟨hxS, y, hxy, hyS⟩
    apply Finset.mem_filter.2
    refine ⟨hxS, ?_⟩
    intro hxI
    have hxcoord := (Finset.mem_filter.1 hxI).2
    have hxycoord := (squareLattice_adj_iff x y).1 hxy
    apply hyS
    rw [hcoords]
    omega

lemma rectangleDualBoundaryCondition_eq_frozen (a : LatticeVertex) (w h : ℕ) :
    rectangleDualBoundaryCondition a w h =
      BoundaryCondition.wired (frozenVertexBoundary (rectangleDualExpanded a w h)) := by
  unfold rectangleDualBoundaryCondition
  congr 1
  ext x
  exact rectangleDualBoundary_eq_vertexBoundary a w h x.val

/-- The genuine free finite-domain law extended by closed exterior edges. -/
def freeDomainProbabilityMeasure (θ : Parameters) (S : Finset LatticeVertex) :
    ProbabilityMeasure LatticeConfiguration :=
  ⟨((law (domainGraph S) θ (BoundaryCondition.free ∅)).map
    (fun A e => decide (e ∈ A.map (frozenEdgeEmbedding S)))).toMeasure,
      PMF.toMeasure.isProbabilityMeasure _⟩

/-- The actual free rectangle law with closed exterior extension. -/
def freeRectangleProbabilityMeasure (θ : Parameters) (a : LatticeVertex) (w h : ℕ) :
    ProbabilityMeasure LatticeConfiguration :=
  freeDomainProbabilityMeasure θ (latticeRectangle a w h)

lemma freeRectangleProbabilityMeasure_box (θ : Parameters) (c : LatticeVertex) (r : ℕ) :
    freeRectangleProbabilityMeasure θ (c.1 - (r : ℤ), c.2 - (r : ℤ)) (2 * r) (2 * r) =
      boxProbabilityMeasure θ c r := by
  unfold freeRectangleProbabilityMeasure
  rw [latticeRectangle_box_eq]
  rfl

/-- The finite true-dual cylinder event, with its original lattice-edge labels. -/
def trueDualCylinderEvent (a : LatticeVertex) (w h : ℕ)
    (F : Finset squareLattice.edgeSet) : Set (Configuration (rectangleDualGraph a w h)) :=
  {A | ∀ e ∈ F, ∀ g, rectangleDualEdgeToSquareEdge a w h g = e → g ∈ A}

attribute [local instance] configurationMeasurableSpace

/-- Cylinder duality, compared to the ordinary expanded-domain wired law. Extra
boundary-to-boundary ambient edges are integrated out by the exact marginal law. -/
theorem freeRectangle_dual_allOpen (θ : Parameters) (a : LatticeVertex) (w h : ℕ)
    (F : Finset squareLattice.edgeSet)
    (hF : ∀ e ∈ F, e ∈ Set.range (rectangleDualEdgeToSquareEdge a w h)) :
    ((freeRectangleProbabilityMeasure θ a w h).map wholePlaneDualConfigurationHomeomorph :
      Measure LatticeConfiguration) (LatticeConfiguration.allOpen F) =
    (wiredDomainProbabilityMeasure (dualParameters θ) (rectangleDualExpanded a w h) :
      Measure LatticeConfiguration) (LatticeConfiguration.allOpen F) := by
  classical
  let E := trueDualCylinderEvent a w h F
  have hprimal : (fun A : Configuration (rectangleGraph a w h) =>
      wholePlaneDualConfigurationHomeomorph (closedRectangleConfiguration a w h A)) ⁻¹'
        LatticeConfiguration.allOpen F =
      (rectanglePrimalDualConfigurationEquiv a w h) ⁻¹' E := by
    ext A
    constructor
    · intro hA e he g hg
      have ht := hA e he
      change wholePlaneDualConfigurationHomeomorph (closedRectangleConfiguration a w h A) e = true at ht
      rw [← hg] at ht
      rw [dual_closedRectangleConfiguration_at a w h A g, decide_eq_true_eq] at ht
      exact ht
    · intro hA e he
      obtain ⟨g, hg⟩ := hF e he
      change wholePlaneDualConfigurationHomeomorph (closedRectangleConfiguration a w h A) e = true
      rw [← hg]
      rw [dual_closedRectangleConfiguration_at a w h A g, decide_eq_true_eq]
      exact hA e he g hg
  have hambient : wiredDomainCylinderEvent (rectangleDualExpanded a w h) F =
      (subgraphConfigurationRestriction (rectangleDualGraph_le_ambient a w h)) ⁻¹' E := by
    ext A
    constructor
    · intro hA e he g hg
      apply (mem_subgraphConfigurationRestriction (rectangleDualGraph_le_ambient a w h) A g).2
      exact hA e he (subgraphEdgeEmbedding (rectangleDualGraph_le_ambient a w h) g) hg
    · intro hA e he f hf
      obtain ⟨g, hg⟩ := hF e he
      have hgf : subgraphEdgeEmbedding (rectangleDualGraph_le_ambient a w h) g = f := by
        apply (frozenEdgeEmbedding (rectangleDualExpanded a w h)).injective
        exact hg.trans hf.symm
      rw [← hgf]
      exact (mem_subgraphConfigurationRestriction _ _ _).1 (hA e he g hg)
  rw [ProbabilityMeasure.toMeasure_map,
    Measure.map_apply wholePlaneDualConfigurationHomeomorph_measurable
      (LatticeConfiguration.allOpen_isClopen F).isOpen.measurableSet]
  change ((law _ θ (BoundaryCondition.free ∅)).map
    (closedRectangleConfiguration a w h)).toMeasure _ = _
  rw [PMF.toMeasure_map_apply _ _ _ measurable_from_top
    ((LatticeConfiguration.allOpen_isClopen F).preimage
      wholePlaneDualConfigurationHomeomorph.continuous).isOpen.measurableSet]
  change (law _ θ (BoundaryCondition.free ∅)).toMeasure
    ((fun A => wholePlaneDualConfigurationHomeomorph (closedRectangleConfiguration a w h A)) ⁻¹'
      LatticeConfiguration.allOpen F) = _
  rw [hprimal, ← PMF.toMeasure_map_apply _ _ _ measurable_from_top (show MeasurableSet E from MeasurableSet.of_discrete),
    rectangleFKLaw_map_primalDualConfigurationEquiv,
    wiredDomainProbabilityMeasure_allOpen, hambient,
    ← rectangleDualBoundaryCondition_eq_frozen]
  change (law (rectangleDualGraph a w h) (dualParameters θ)
    (rectangleDualBoundaryCondition a w h)).toMeasure E =
      (law (rectangleDualAmbientGraph a w h) (dualParameters θ)
        (rectangleDualBoundaryCondition a w h)).toMeasure
          ((subgraphConfigurationRestriction (rectangleDualGraph_le_ambient a w h)) ⁻¹' E)
  rw [← PMF.toMeasure_map_apply _ _ _ measurable_from_top (show MeasurableSet E from MeasurableSet.of_discrete),
    rectangleDualAmbient_law_restrict_to_dual]

end
end PottsDiscontinuity.Duality
