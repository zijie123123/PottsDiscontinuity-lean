module

public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import Mathlib.Topology.Homotopy.Lifting
public import Mathlib.Topology.Homotopy.Path
public import PottsDiscontinuity.Duality.FreeAssociation
public import PottsDiscontinuity.Duality.InfiniteDuality

/-! Applying the planar dual transform twice translates face-base coordinates.
Translation invariance therefore also gives wired-to-free infinite-volume duality. -/

@[expose] public section

namespace PottsDiscontinuity.Duality
open FK FK.Medial MeasureTheory
noncomputable section

lemma dualConfiguration_twice (ω : LatticeConfiguration) :
    wholePlaneDualConfigurationHomeomorph (wholePlaneDualConfigurationHomeomorph ω) =
      latticeConfigurationIsoHomeomorph (latticeTranslationIso (-1,-1)) ω := by
  funext e
  obtain ⟨b, rfl⟩ := wholePlaneBondEdgeEquiv.surjective e
  change latticeConfigurationBondState
    (wholePlaneDualConfigurationHomeomorph (wholePlaneDualConfigurationHomeomorph ω)) b = _
  rw [wholePlaneDualConfigurationHomeomorph_bondState,
    wholePlaneDualConfigurationHomeomorph_bondState]
  simp only [Bool.not_not, latticeConfigurationBondState,
    latticeConfigurationIsoHomeomorph_apply]
  congr 1
  apply Subtype.ext
  rcases b with ⟨⟨x,y⟩, ax⟩
  cases ax <;>
    simp [primalBondOfDual, wholePlaneBondEdgeEquiv, latticeBondEdge, LatticeBond.toSym2, LatticeBond.source,
      LatticeBond.target, SimpleGraph.Iso.mapEdgeSet_apply, SimpleGraph.Hom.mapEdgeSet_coe,
      latticeTranslationIso, latticeTranslate]

/-- The wired measure at p* maps to the free measure at p under the actual dual
transform. Its square is the harmless lattice translation (-1,-1). -/
theorem wired_map_dual_eq_free (θ : Parameters)
    (μ₀ μ₁ : Measure LatticeConfiguration)
    (hμ₀ : IsRCInfiniteVolumeLimit θ.toP θ.toQ 0 μ₀)
    (hμ₁ : IsRCInfiniteVolumeLimit (dualParameters θ).toP (dualParameters θ).toQ 1 μ₁) :
    μ₁.map wholePlaneDualConfigurationHomeomorph = μ₀ := by
  rw [← free_map_dual_eq_wired θ μ₀ μ₁ hμ₀ hμ₁,
    Measure.map_map wholePlaneDualConfigurationHomeomorph_measurable
      wholePlaneDualConfigurationHomeomorph_measurable]
  have heq : (wholePlaneDualConfigurationHomeomorph ∘ wholePlaneDualConfigurationHomeomorph) =
      latticeConfigurationIsoHomeomorph (latticeTranslationIso (-1,-1)) :=
    funext dualConfiguration_twice
  rw [heq]
  exact free_limit_map_latticeIso θ μ₀ hμ₀ (latticeTranslationIso (-1,-1))
    (fun c v r => mem_latticeBox_translate_iff (-1,-1) c v r)

end
end PottsDiscontinuity.Duality
