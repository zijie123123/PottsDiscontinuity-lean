/- Adapted from an earlier, unpublished formalization of the planar FK model by the same author.
Adaptation: Namespace and import relocation only. -/
module

public import Mathlib.Tactic
public import PottsDiscontinuity.TorusTopology.PlanarParafermionicCoverFaceUnionConnectivity

@[expose] public section

namespace PottsDiscontinuity.TorusTopology.Planar.Medial

open PottsDiscontinuity.TorusTopology.Planar

def faceVertex0 {n : ℕ} (i : ParafermionicCoverFiniteFaceTopIndex n) :
    ParafermionicCoverBoxVertex n :=
  ⟨i.1, by
    have h := parafermionicCoverFiniteFaceDart_endpoints_mem n i.1 i.2
      (e := (i.1, parafermionicCoverFaceRightLift i.1.1.1 i.1.1.2 i.1.2)) (by
        simp [parafermionicCoverFiniteFaceDarts])
    exact h.1⟩

def faceVertex1 {n : ℕ} (i : ParafermionicCoverFiniteFaceTopIndex n) :
    ParafermionicCoverBoxVertex n :=
  ⟨parafermionicCoverFaceRightLift i.1.1.1 i.1.1.2 i.1.2,
    (parafermionicCoverFiniteFaceDart_endpoints_mem n i.1 i.2
      (e := (i.1, parafermionicCoverFaceRightLift i.1.1.1 i.1.1.2 i.1.2)) (by
        simp [parafermionicCoverFiniteFaceDarts])).2⟩

def faceVertex2 {n : ℕ} (i : ParafermionicCoverFiniteFaceTopIndex n) :
    ParafermionicCoverBoxVertex n :=
  ⟨parafermionicCoverFaceRightUpLift i.1.1.1 i.1.1.2 i.1.2,
    (parafermionicCoverFiniteFaceTopEdge_endpoints_mem n i.1 i.2).1⟩

def faceVertex3 {n : ℕ} (i : ParafermionicCoverFiniteFaceTopIndex n) :
    ParafermionicCoverBoxVertex n :=
  ⟨parafermionicCoverFaceRightUpLeftLift i.1.1.1 i.1.1.2 i.1.2,
    (parafermionicCoverFiniteFaceTopEdge_endpoints_mem n i.1 i.2).2⟩

noncomputable def faceVertices {n : ℕ}
    (i : ParafermionicCoverFiniteFaceTopIndex n) : Finset (ParafermionicCoverBoxVertex n) := by
  classical
  exact ([faceVertex0 i, faceVertex1 i, faceVertex2 i, faceVertex3 i] :
    List (ParafermionicCoverBoxVertex n)).toFinset

private theorem faceBoundary_edgeSet_local {n : ℕ}
    (i : ParafermionicCoverFiniteFaceTopIndex n) :
    (parafermionicCoverFiniteFaceBoundaryGraph i.1 i.2).edgeSet =
      {s(faceVertex0 i, faceVertex1 i), s(faceVertex1 i, faceVertex2 i),
       s(faceVertex2 i, faceVertex3 i), s(faceVertex3 i, faceVertex0 i)} := by
  rw [parafermionicCoverFiniteFaceBoundaryGraph_edgeSet]
  rfl

private theorem faceVertices_iff_incident {n : ℕ}
    (i : ParafermionicCoverFiniteFaceTopIndex n) (v : ParafermionicCoverBoxVertex n) :
    v ∈ faceVertices i ↔
      ∃ w, (parafermionicCoverFiniteFaceBoundaryGraph i.1 i.2).Adj v w := by
  classical
  constructor
  · intro hv
    simp [faceVertices] at hv
    rcases hv with hv | hv | hv | hv
    · subst v
      refine ⟨faceVertex1 i, ?_⟩
      exact (parafermionicCoverFiniteFaceBoundaryGraph i.1 i.2).mem_edgeSet.mp (by
        rw [faceBoundary_edgeSet_local]
        simp)
    · subst v
      refine ⟨faceVertex0 i, ?_⟩
      exact (parafermionicCoverFiniteFaceBoundaryGraph i.1 i.2).mem_edgeSet.mp (by
        rw [faceBoundary_edgeSet_local]
        simp)
    · subst v
      refine ⟨faceVertex3 i, ?_⟩
      exact (parafermionicCoverFiniteFaceBoundaryGraph i.1 i.2).mem_edgeSet.mp (by
        rw [faceBoundary_edgeSet_local]
        simp)
    · subst v
      refine ⟨faceVertex2 i, ?_⟩
      exact (parafermionicCoverFiniteFaceBoundaryGraph i.1 i.2).mem_edgeSet.mp (by
        rw [faceBoundary_edgeSet_local]
        simp)
  · rintro ⟨w, hvw⟩
    have hed : s(v,w) ∈
        (parafermionicCoverFiniteFaceBoundaryGraph i.1 i.2).edgeSet :=
      (parafermionicCoverFiniteFaceBoundaryGraph i.1 i.2).mem_edgeSet.mpr hvw
    rw [faceBoundary_edgeSet_local] at hed
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hed
    rcases hed with hed | hed | hed | hed
    all_goals
      rcases Sym2.eq_iff.mp hed with ⟨hvw, _⟩ | ⟨hvw, _⟩ <;> subst v <;>
        simp [faceVertices]

theorem parafermionicCoverFiniteFaceBoundaryGraph_vertex_incident_iff_fourCorners
    {n : ℕ} (i : ParafermionicCoverFiniteFaceTopIndex n)
    (v : ParafermionicCoverBoxVertex n) :
    (∃ w, (parafermionicCoverFiniteFaceBoundaryGraph i.1 i.2).Adj v w) ↔
      v.1 = i.1 ∨
      v.1 = parafermionicCoverFaceRightLift i.1.1.1 i.1.1.2 i.1.2 ∨
      v.1 = parafermionicCoverFaceRightUpLift i.1.1.1 i.1.1.2 i.1.2 ∨
      v.1 = parafermionicCoverFaceRightUpLeftLift i.1.1.1 i.1.1.2 i.1.2 := by
  rw [← faceVertices_iff_incident]
  simp [faceVertices, faceVertex0, faceVertex1, faceVertex2, faceVertex3]
  simp only [Subtype.ext_iff]

/-- The selected actual faces incident to a box vertex, using adjacency in the
actual lifted boundary graph of each selected face. -/
noncomputable def parafermionicCoverFiniteFaceSelectedIncidentVertices {n : ℕ}
    (S : Finset (ParafermionicCoverFiniteFaceTopIndex n))
    (v : ParafermionicCoverBoxVertex n) : Finset (ParafermionicCoverFiniteFaceTopIndex n) := by
  classical
  exact S.filter fun i =>
    ∃ w, (parafermionicCoverFiniteFaceBoundaryGraph i.1 i.2).Adj v w

theorem parafermionicCoverFiniteFaceUnionCarrier_iff_incidentVertices_nonempty {n : ℕ}
    (S : Finset (ParafermionicCoverFiniteFaceTopIndex n))
    (v : ParafermionicCoverBoxVertex n) :
    v ∈ parafermionicCoverFiniteFaceUnionCarrier S ↔
      (parafermionicCoverFiniteFaceSelectedIncidentVertices S v).Nonempty := by
  classical
  constructor
  · rintro ⟨w, i, hi, hadj⟩
    refine ⟨i, ?_⟩
    exact Finset.mem_filter.mpr ⟨hi, ⟨w, hadj⟩⟩
  · intro h
    rcases h with ⟨i, hi⟩
    rcases Finset.mem_filter.mp hi with ⟨hiS, w, hadj⟩
    exact ⟨w, i, hiS, hadj⟩

private theorem faceVertices_card_four {n : ℕ}
    (i : ParafermionicCoverFiniteFaceTopIndex n) : (faceVertices i).card = 4 := by
  classical
  let f := i.1
  obtain ⟨q, hcycle, hlength, hsupp⟩ :=
    parafermionicCoverFiniteOrdinaryFace_has_cycle n f
      (Finset.mem_filter.mp i.2).1 i.2
  have hsupp' : q.support =
      [faceVertex0 i, faceVertex1 i, faceVertex2 i, faceVertex3 i, faceVertex0 i] := by
    apply Function.Injective.list_map Subtype.val_injective
    simpa [faceVertex0, faceVertex1, faceVertex2, faceVertex3] using hsupp
  have hnodup : ([faceVertex0 i, faceVertex1 i, faceVertex2 i, faceVertex3 i] :
      List (ParafermionicCoverBoxVertex n)).Nodup := by
    have htail : ([faceVertex1 i, faceVertex2 i, faceVertex3 i, faceVertex0 i] :
        List (ParafermionicCoverBoxVertex n)).Nodup := by
      simpa [hsupp'] using hcycle.support_nodup
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil] at htail ⊢
    aesop
  exact List.toFinset_card_of_nodup hnodup

theorem parafermionicCoverFiniteFaceSetVertexIncidence_count {n : ℕ}
    (S : Finset (ParafermionicCoverFiniteFaceTopIndex n)) :
    ∑ v : ParafermionicCoverBoxVertex n,
      (parafermionicCoverFiniteFaceSelectedIncidentVertices S v).card = 4 * S.card := by
  classical
  let I : ParafermionicCoverBoxVertex n → Finset (ParafermionicCoverFiniteFaceTopIndex n) :=
    fun v => parafermionicCoverFiniteFaceSelectedIncidentVertices S v
  have hcard (v : ParafermionicCoverBoxVertex n) :
      (I v).card = ∑ i ∈ S, if v ∈ faceVertices i then 1 else 0 := by
    rw [show I v = S.filter (fun i => v ∈ faceVertices i) by
      ext i
      simp [I, parafermionicCoverFiniteFaceSelectedIncidentVertices,
        faceVertices_iff_incident]]
    rw [Finset.card_filter]
  calc
    _ = ∑ v : ParafermionicCoverBoxVertex n, ∑ i ∈ S,
        if v ∈ faceVertices i then 1 else 0 := by
          apply Finset.sum_congr rfl
          intro v hv
          exact hcard v
    _ = ∑ i ∈ S, ∑ v : ParafermionicCoverBoxVertex n,
        if v ∈ faceVertices i then 1 else 0 := by
          rw [Finset.sum_comm]
    _ = ∑ i ∈ S, (faceVertices i).card := by
          apply Finset.sum_congr rfl
          intro i hi
          rw [Finset.sum_boole]
          apply congrArg Finset.card
          ext v
          simp
    _ = 4 * S.card := by
          simp_rw [faceVertices_card_four]
          simp [mul_comm]

end PottsDiscontinuity.TorusTopology.Planar.Medial
