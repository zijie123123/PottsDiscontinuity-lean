/- Adapted from an earlier, unpublished formalization of the planar FK model by the same author.
Adaptation: Namespace/import relocation; the incidence-card proof uses only actual incident faces, eliminating the original nonincident zero fallback. -/
module

public import PottsDiscontinuity.TorusTopology.PlanarParafermionicCoverFaceCorners
public import Mathlib.Tactic

@[expose] public section

namespace PottsDiscontinuity.TorusTopology.Planar.Medial

open PottsDiscontinuity.TorusTopology.Planar

/-- Actual corner labels contributed at a box vertex by selected retained
lifted faces. -/
noncomputable def parafermionicCoverFiniteFaceSelectedCorners {n : ℕ}
    (S : Finset (ParafermionicCoverFiniteFaceTopIndex n))
    (v : ParafermionicCoverBoxVertex n) : Finset (Fin 4) := by
  classical
  exact Finset.univ.filter fun c =>
    ∃ i ∈ S, parafermionicCoverFaceCorner i.1 c = v.1

theorem parafermionicCoverFiniteFaceSelectedCorners_mem_iff {n : ℕ}
    (S : Finset (ParafermionicCoverFiniteFaceTopIndex n))
    (v : ParafermionicCoverBoxVertex n) (c : Fin 4) :
    c ∈ parafermionicCoverFiniteFaceSelectedCorners S v ↔
      ∃ i ∈ S, parafermionicCoverFaceCorner i.1 c = v.1 := by
  classical
  simp [parafermionicCoverFiniteFaceSelectedCorners]

/-- Counting actual selected corners is bijective with actual incident faces.
The corner map is defined only on incident faces, with no default value. -/
theorem parafermionicCoverFiniteFaceSelectedCorners_card {n : ℕ}
    (S : Finset (ParafermionicCoverFiniteFaceTopIndex n))
    (v : ParafermionicCoverBoxVertex n) :
    (parafermionicCoverFiniteFaceSelectedCorners S v).card =
      (parafermionicCoverFiniteFaceSelectedIncidentVertices S v).card := by
  classical
  let I := ↥(parafermionicCoverFiniteFaceSelectedIncidentVertices S v)
  let C := ↥(parafermionicCoverFiniteFaceSelectedCorners S v)
  have hex (i : I) : ∃! c : Fin 4, parafermionicCoverFaceCorner i.val.val c = v.val := by
    obtain ⟨c,hc⟩ := (parafermionicCoverFiniteFaceBoundaryGraph_vertex_incident_iff_faceCorner i.val v).mp
      (Finset.mem_filter.mp i.property).2
    exact ⟨c,hc,fun d hd => parafermionicCoverFaceCorner_injective_label i.val.val (hd.trans hc.symm)⟩
  choose c hc using fun i : I => (hex i).exists
  let F : I → C := fun i => ⟨c i,
    (parafermionicCoverFiniteFaceSelectedCorners_mem_iff S v (c i)).mpr
      ⟨i.val,(Finset.mem_filter.mp i.property).1,hc i⟩⟩
  have hinj : Function.Injective F := by
    intro i j he
    have hlabel : c i = c j := congrArg Subtype.val he
    apply Subtype.ext
    apply Subtype.ext
    apply parafermionicCoverFaceCorner_injective_face (c i)
    change parafermionicCoverFaceCorner i.val.val (c i) =
      parafermionicCoverFaceCorner j.val.val (c i)
    rw [hc i,hlabel,hc j]
  have hsurj : Function.Surjective F := by
    intro q
    obtain ⟨i,hiS,hiq⟩ := (parafermionicCoverFiniteFaceSelectedCorners_mem_iff S v q.val).mp q.property
    have hi : i ∈ parafermionicCoverFiniteFaceSelectedIncidentVertices S v :=
      Finset.mem_filter.mpr ⟨hiS,
        (parafermionicCoverFiniteFaceBoundaryGraph_vertex_incident_iff_faceCorner i v).mpr ⟨q.val,hiq⟩⟩
    let ii : I := ⟨i,hi⟩
    refine ⟨ii,Subtype.ext ?_⟩
    change c ii = q.val
    exact parafermionicCoverFaceCorner_injective_label i.val ((hc ii).trans hiq.symm)
  have hh := Fintype.card_congr (Equiv.ofBijective F ⟨hinj,hsurj⟩)
  simpa only [I,C,Fintype.card_coe] using hh.symm

theorem parafermionicCoverFiniteFaceSelectedCorners_nonempty_iff_unionCarrier
    {n : ℕ} (S : Finset (ParafermionicCoverFiniteFaceTopIndex n))
    (v : ParafermionicCoverBoxVertex n) :
    (parafermionicCoverFiniteFaceSelectedCorners S v).Nonempty ↔
      v ∈ parafermionicCoverFiniteFaceUnionCarrier S := by
  constructor
  · intro h
    apply (parafermionicCoverFiniteFaceUnionCarrier_iff_incidentVertices_nonempty S v).2
    have hpos : 0 <
        (parafermionicCoverFiniteFaceSelectedIncidentVertices S v).card := by
      rw [← parafermionicCoverFiniteFaceSelectedCorners_card]
      exact Finset.card_pos.mpr h
    exact Finset.card_pos.mp hpos
  · intro h
    have hi :=
      (parafermionicCoverFiniteFaceUnionCarrier_iff_incidentVertices_nonempty S v).1 h
    have hpos := Finset.card_pos.mpr hi
    rw [← parafermionicCoverFiniteFaceSelectedCorners_card] at hpos
    exact Finset.card_pos.mp hpos

end PottsDiscontinuity.TorusTopology.Planar.Medial
