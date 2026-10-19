module

public import PottsDiscontinuity.Duality.FiniteDuality
public import PottsDiscontinuity.Duality.RectangleDualAmbient
public import PottsDiscontinuity.FK.FrozenLimitBridge
public import PottsDiscontinuity.FK.SubgraphComparison

/-! Edge-by-edge bridge between finite complementary duality and the actual
whole-plane configuration homeomorphism. -/

@[expose] public section

namespace PottsDiscontinuity.Duality

open FK FK.Medial
noncomputable section

/-- Closed exterior extension of a finite rectangle sample. -/
def closedRectangleConfiguration (a : LatticeVertex) (w h : ℕ)
    (A : Configuration (rectangleGraph a w h)) : LatticeConfiguration :=
  fun e => decide (e ∈ A.map (frozenEdgeEmbedding (latticeRectangle a w h)))

@[simp] lemma closedRectangleConfiguration_at (a : LatticeVertex) (w h : ℕ)
    (A : Configuration (rectangleGraph a w h)) (f : (rectangleGraph a w h).edgeSet) :
    closedRectangleConfiguration a w h A
      (rectanglePrimalEdgeToSquareEdge a w h f) = decide (f ∈ A) := by
  have he : rectanglePrimalEdgeToSquareEdge a w h f =
      frozenEdgeEmbedding (latticeRectangle a w h) f := by apply Subtype.ext; rfl
  rw [he]
  unfold closedRectangleConfiguration
  congr 1
  apply propext
  constructor
  · intro hf
    obtain ⟨g, hg, hgf⟩ := Finset.mem_map.mp hf
    exact (frozenEdgeEmbedding (latticeRectangle a w h)).injective hgf ▸ hg
  · intro hf
    exact Finset.mem_map.mpr ⟨f, hf, rfl⟩

/-- The original lattice edge underlying a true finite dual edge. -/
def rectangleDualEdgeToSquareEdge (a : LatticeVertex) (w h : ℕ) :
    (rectangleDualGraph a w h).edgeSet ↪ squareLattice.edgeSet :=
  (subgraphEdgeEmbedding (rectangleDualGraph_le_ambient a w h)).trans
    (frozenEdgeEmbedding (rectangleDualExpanded a w h))

lemma rectangleDualEdgeToSquareEdge_carrier (a : LatticeVertex) (w h : ℕ)
    (e : RectangleDualEdgeCarrier a w h) :
    rectangleDualEdgeToSquareEdge a w h (rectangleDualGraphEdgeEquiv a w h e) =
      latticeBondEdge e.crossingBond := by
  apply Subtype.ext
  rfl

/-- Each sampled dual edge has the complement of its original crossing primal state. -/
theorem dual_closedRectangleConfiguration_at (a : LatticeVertex) (w h : ℕ)
    (A : Configuration (rectangleGraph a w h)) (g : (rectangleDualGraph a w h).edgeSet) :
    wholePlaneDualConfigurationHomeomorph (closedRectangleConfiguration a w h A)
      (rectangleDualEdgeToSquareEdge a w h g) =
        decide (g ∈ rectanglePrimalDualConfigurationEquiv a w h A) := by
  classical
  obtain ⟨e, rfl⟩ := (rectangleDualGraphEdgeEquiv a w h).surjective g
  rw [rectangleDualEdgeToSquareEdge_carrier]
  change latticeConfigurationBondState
    (wholePlaneDualConfigurationHomeomorph (closedRectangleConfiguration a w h A))
      e.crossingBond = _
  rw [wholePlaneDualConfigurationHomeomorph_bondState]
  change Bool.not (closedRectangleConfiguration a w h A
    (latticeBondEdge (primalBondOfDual e.crossingBond))) = _
  rw [rectangleDualEdge_crossing_originalEdge]
  rw [closedRectangleConfiguration_at a w h A e.primalEdge]
  simp only [mem_rectanglePrimalDualConfigurationEquiv]
  by_cases he : e.primalEdge ∈ A <;> simp [he] <;> exact he

end
end PottsDiscontinuity.Duality
