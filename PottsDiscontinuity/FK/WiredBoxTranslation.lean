/- Adapted from an earlier, unpublished formalization of the planar FK model by the same author.
The finite laws use wired vertex boundaries and open exterior extension. -/
module

public import PottsDiscontinuity.FK.WiredBoxLaw
public import PottsDiscontinuity.FK.BoxTranslation
public import PottsDiscontinuity.FK.BoundaryPartitionLaw

@[expose] public section

namespace PottsDiscontinuity.FK

open MeasureTheory
noncomputable section

/-- Translation preserves the frozen vertex boundary of every lattice box. -/
theorem mem_vertexBoundary_latticeBox_translate_iff (a c v : LatticeVertex) (r : ℕ) :
    latticeTranslate a v ∈ vertexBoundary (latticeBox (latticeTranslate a c) r) ↔
      v ∈ vertexBoundary (latticeBox c r) := by
  simp only [vertexBoundary, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨hv, w, hadj, hw⟩
    have hcancel : latticeTranslate a (latticeTranslate (-a) w) = w :=
      (latticeTranslationIso a).apply_symm_apply w
    refine ⟨(mem_latticeBox_translate_iff a c v r).mp hv,
      latticeTranslate (-a) w, ?_, ?_⟩
    · apply (squareLattice_adj_translate_iff a v (latticeTranslate (-a) w)).mp
      simpa only [hcancel] using hadj
    · intro hm
      apply hw
      simpa only [hcancel] using
        (mem_latticeBox_translate_iff a c (latticeTranslate (-a) w) r).mpr hm
  · rintro ⟨hv, w, hadj, hw⟩
    refine ⟨(mem_latticeBox_translate_iff a c v r).mpr hv,
      latticeTranslate a w, (squareLattice_adj_translate_iff a v w).mpr hadj, ?_⟩
    exact fun hm => hw ((mem_latticeBox_translate_iff a c w r).mp hm)

/-- Transporting a wired box boundary gives the translated wired partition. -/
theorem boundaryConditionIso_wired_box_partition (a c : LatticeVertex) (r : ℕ) :
    (boundaryConditionIso (boxVertexTranslationIso a c r)
      (BoundaryCondition.wired (boxVertexBoundary c r))).partition =
        (BoundaryCondition.wired (boxVertexBoundary (latticeTranslate a c) r)).partition := by
  let e := boxVertexTranslationIso a c r
  have hmem (u : BoxVertex (latticeTranslate a c) r) :
      e.symm u ∈ boxVertexBoundary c r ↔
        u ∈ boxVertexBoundary (latticeTranslate a c) r := by
    change latticeTranslate (-a) u.val ∈ vertexBoundary (latticeBox c r) ↔
      u.val ∈ vertexBoundary (latticeBox (latticeTranslate a c) r)
    have hcancel : latticeTranslate a (latticeTranslate (-a) u.val) = u.val :=
      (latticeTranslationIso a).apply_symm_apply u.val
    exact ((mem_vertexBoundary_latticeBox_translate_iff a c
      (latticeTranslate (-a) u.val) r).trans (Iff.rfl)).symm.trans (by rw [hcancel])
  apply Setoid.ext
  intro u v
  change (e.symm u = e.symm v ∨
    e.symm u ∈ boxVertexBoundary c r ∧ e.symm v ∈ boxVertexBoundary c r) ↔
    (u = v ∨ u ∈ boxVertexBoundary (latticeTranslate a c) r ∧
      v ∈ boxVertexBoundary (latticeTranslate a c) r)
  exact or_congr e.symm.injective.eq_iff (and_congr (hmem u) (hmem v))

/-- Open extension commutes with the actual lattice-edge translation. -/
theorem wiredBoxConfiguration_translation_commute (a c : LatticeVertex) (r : ℕ)
    (A : Configuration (boxGraph c r)) :
    wiredBoxConfiguration (latticeTranslate a c) r
        (configurationIso (boxVertexTranslationIso a c r) A) =
      latticeConfigurationTranslate a (wiredBoxConfiguration c r A) := by
  classical
  let E := SimpleGraph.Iso.mapEdgeSet (latticeTranslationIso a)
  let I := SimpleGraph.Iso.mapEdgeSet (boxVertexTranslationIso a c r)
  funext e
  obtain ⟨e, rfl⟩ := E.surjective e
  have htranslate (ω : LatticeConfiguration) :
      latticeConfigurationTranslate a ω (E e) = ω e := by
    exact Homeomorph.piCongrLeft_apply_apply (Y := fun _ => Bool) E ω e
  rw [htranslate]
  apply Bool.eq_iff_iff.mpr
  rw [wiredBoxConfiguration_open_iff, wiredBoxConfiguration_open_iff]
  constructor
  · intro h f hf
    have ht : boxEdgeEmbedding (latticeTranslate a c) r (I f) = E e := by
      rw [boxEdgeEmbedding_translation, hf]
    have hm := h (I f) ht
    change I f ∈ A.map I.toEmbedding at hm
    rwa [Finset.mem_map_equiv, Equiv.symm_apply_apply] at hm
  · intro h f hf
    obtain ⟨g, rfl⟩ := I.surjective f
    have hg : boxEdgeEmbedding c r g = e := by
      apply E.injective
      exact (boxEdgeEmbedding_translation a c r g).symm.trans hf
    have hm := h g hg
    change I g ∈ A.map I.toEmbedding
    rwa [Finset.mem_map_equiv, Equiv.symm_apply_apply]

private theorem pmf_map_commute {α β γ δ : Type*}
    (μ : PMF α) (ν : PMF β) (f : α → γ) (g : β → δ)
    (e : α → β) (T : γ → δ) (he : μ.map e = ν)
    (hcomm : ∀ x, g (e x) = T (f x)) :
    (μ.map f).map T = ν.map g := by
  rw [← he, PMF.map_comp, PMF.map_comp]
  apply congrArg (fun k => μ.map k)
  exact funext fun x => (hcomm x).symm

/-- The finite wired PMF translates to the box with translated center. -/
theorem wiredBoxLaw_translation_map (θ : Parameters) (a c : LatticeVertex) (r : ℕ) :
    PMF.map (latticeConfigurationTranslate a) (wiredBoxLaw θ c r) =
      wiredBoxLaw θ (latticeTranslate a c) r := by
  exact pmf_map_commute
    (law (boxGraph c r) θ (BoundaryCondition.wired (boxVertexBoundary c r)))
    (law (boxGraph (latticeTranslate a c) r) θ
      (BoundaryCondition.wired (boxVertexBoundary (latticeTranslate a c) r)))
    (wiredBoxConfiguration c r) (wiredBoxConfiguration (latticeTranslate a c) r)
    (configurationIso (boxVertexTranslationIso a c r)) (latticeConfigurationTranslate a)
    ((law_configurationIso_map θ (boxVertexTranslationIso a c r)
      (BoundaryCondition.wired (boxVertexBoundary c r))).trans
        (law_eq_of_boundary_partition_eq θ _ _
          (boundaryConditionIso_wired_box_partition a c r)))
    (wiredBoxConfiguration_translation_commute a c r)

/-- Translation of the finite wired law as a probability measure. -/
theorem wiredBoxProbabilityMeasure_translation_map (θ : Parameters)
    (a c : LatticeVertex) (r : ℕ) :
    ProbabilityMeasure.map (wiredBoxProbabilityMeasure θ c r)
        (latticeConfigurationTranslate a) =
      wiredBoxProbabilityMeasure θ (latticeTranslate a c) r := by
  apply ProbabilityMeasure.toMeasure_injective
  change Measure.map (latticeConfigurationTranslate a) (wiredBoxLaw θ c r).toMeasure =
    (wiredBoxLaw θ (latticeTranslate a c) r).toMeasure
  rw [PMF.toMeasure_map _ _ (latticeConfigurationTranslate_measurable a)]
  exact congrArg PMF.toMeasure (wiredBoxLaw_translation_map θ a c r)

end
end PottsDiscontinuity.FK
