/- Adapted from an earlier, unpublished formalization of the planar FK model by the same author.
The comparison is reversed for wired boundaries and open exterior extension.
The interior-closure and outer-boundary avoidance proofs are original. -/
module

public import PottsDiscontinuity.FK.WiredBoxLaw
public import PottsDiscontinuity.FK.BoxComparison
public import PottsDiscontinuity.FK.EmbeddedClosedInteriorOuterComparison

/-! Wired box laws decrease on increasing cylinder events as the domain grows. -/

@[expose] public section

namespace PottsDiscontinuity.FK

open MeasureTheory
noncomputable section

private theorem boxInterior_neighbor_closed {c d : LatticeVertex} {r s : ℕ}
    (hbox : latticeBox c r ⊆ latticeBox d s)
    {x : BoxVertex c r} (hx : x ∉ boxVertexBoundary c r)
    {y : BoxVertex d s} (hxy : (boxGraph d s).Adj (boxVertexEmbedding hbox x) y) :
    ∃ z : BoxVertex c r, boxVertexEmbedding hbox z = y ∧ (boxGraph c r).Adj x z := by
  have hy : y.val ∈ latticeBox c r := by
    by_contra hn
    apply hx
    exact ⟨x.property, y.val, hxy, hn⟩
  exact ⟨⟨y.val, hy⟩, Subtype.ext rfl, hxy⟩

private theorem boxInterior_avoids_outerBoundary {c d : LatticeVertex} {r s : ℕ}
    (hbox : latticeBox c r ⊆ latticeBox d s)
    {x : BoxVertex c r} (hx : x ∉ boxVertexBoundary c r) :
    boxVertexEmbedding hbox x ∉
      (BoundaryCondition.wired (boxVertexBoundary d s)).boundary := by
  rintro ⟨_, y, hxy, hy⟩
  apply hx
  exact ⟨x.property, y, hxy, fun hys => hy (hbox hys)⟩

private theorem wiredBoxEdgeEmbedding_compatible {c d : LatticeVertex} {r s : ℕ}
    (hbox : latticeBox c r ⊆ latticeBox d s)
    (hGH : (boxGraph c r).map (boxVertexEmbedding hbox) ≤ boxGraph d s)
    (e : (boxGraph c r).edgeSet) :
    boxEdgeEmbedding d s (embeddedEdgeEmbedding (boxGraph c r) (boxGraph d s)
      (boxVertexEmbedding hbox) hGH e) = boxEdgeEmbedding c r e := by
  apply Subtype.ext
  change Sym2.map (fun v : BoxVertex d s => v.val)
      (Sym2.map (boxVertexEmbedding hbox) e.val) =
    Sym2.map (fun v : BoxVertex c r => v.val) e.val
  rw [Sym2.map_map]
  congr 1

private theorem wiredBoxCylinderEvent_restrict_of_large
    {c d : LatticeVertex} {r s : ℕ}
    (hbox : latticeBox c r ⊆ latticeBox d s)
    (hGH : (boxGraph c r).map (boxVertexEmbedding hbox) ≤ boxGraph d s)
    (F : Finset squareLattice.edgeSet) (A : Configuration (boxGraph d s))
    (hA : A ∈ wiredBoxCylinderEvent d s F) :
    embeddedConfigurationRestriction (boxGraph c r) (boxGraph d s)
      (boxVertexEmbedding hbox) hGH A ∈ wiredBoxCylinderEvent c r F := by
  intro e he f hf
  rw [mem_embeddedConfigurationRestriction]
  exact hA e he
    (embeddedEdgeEmbedding (boxGraph c r) (boxGraph d s) (boxVertexEmbedding hbox) hGH f)
    ((wiredBoxEdgeEmbedding_compatible hbox hGH f).trans hf)

/-- Wired all-open cylinder probabilities decrease under box containment.
Open exterior extension makes this valid even before the cylinder lies inside
the smaller finite volume. -/
theorem wiredBoxProbabilityMeasure_allOpen_antitone (θ : Parameters)
    (c d : LatticeVertex) (r s : ℕ)
    (hbox : latticeBox c r ⊆ latticeBox d s) (F : Finset squareLattice.edgeSet) :
    (wiredBoxProbabilityMeasure θ d s : Measure LatticeConfiguration)
        (LatticeConfiguration.allOpen F) ≤
      (wiredBoxProbabilityMeasure θ c r : Measure LatticeConfiguration)
        (LatticeConfiguration.allOpen F) := by
  classical
  let f := boxVertexEmbedding hbox
  have hGH : (boxGraph c r).map f ≤ boxGraph d s := boxGraph_map_boxVertexEmbedding hbox
  have hcmp := embeddedConfigurationRestriction_preimage_measure_le_wired_of_closedInterior
    f hGH θ (BoundaryCondition.wired (boxVertexBoundary d s)) (boxVertexBoundary c r)
    (fun _ hx _ hxy => boxInterior_neighbor_closed hbox hx hxy)
    (fun _ hx => boxInterior_avoids_outerBoundary hbox hx)
    (wiredBoxCylinderEvent c r F) (wiredBoxCylinderEvent_upper c r F)
  have hsub : wiredBoxCylinderEvent d s F ⊆
      {A | embeddedConfigurationRestriction (boxGraph c r) (boxGraph d s)
        f hGH A ∈ wiredBoxCylinderEvent c r F} :=
    fun A hA => wiredBoxCylinderEvent_restrict_of_large hbox hGH F A hA
  rw [wiredBoxProbabilityMeasure_allOpen, wiredBoxProbabilityMeasure_allOpen]
  apply (ENNReal.toReal_le_toReal (measure_ne_top _ _) (measure_ne_top _ _)).mp
  exact (ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono hsub)).trans hcmp

end
end PottsDiscontinuity.FK
