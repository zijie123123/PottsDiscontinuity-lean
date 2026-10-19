/- Adapted from an earlier, unpublished formalization of the planar FK model by the same author.
Adaptation: Namespace and import relocation only. -/
module

public import Mathlib.Tactic
public import PottsDiscontinuity.TorusTopology.PlanarParafermionicCoverFaceSetEdgeCount
public import PottsDiscontinuity.TorusTopology.PlanarParafermionicCoverSimpleCycleComplementConnectivity

@[expose] public section

namespace PottsDiscontinuity.TorusTopology.Planar.Medial

open PottsDiscontinuity.TorusTopology.Planar
open SimpleGraph

private theorem fillingContainment_selectedIncident_mem {n : ℕ}
    (S : Finset (ParafermionicCoverFiniteFaceTopIndex n))
    (e : Sym2 (ParafermionicCoverBoxVertex n))
    (i : ParafermionicCoverFiniteFaceTopIndex n) :
    i ∈ parafermionicCoverFiniteFaceSelectedIncidentFaces S e ↔
      i ∈ S ∧ e ∈ (parafermionicCoverFiniteFaceBoundaryGraph i.1 i.2).edgeSet := by
  classical
  simp [parafermionicCoverFiniteFaceSelectedIncidentFaces,
    parafermionicCoverFiniteFaceIncidentFaces, and_comm]

private theorem fillingContainment_support_mem_iff {n : ℕ}
    (S : Finset (ParafermionicCoverFiniteFaceTopIndex n))
    (e : Sym2 (ParafermionicCoverBoxVertex n)) :
    e ∈ parafermionicCoverFiniteFaceSetEdgeSupport S ↔
      (parafermionicCoverFiniteFaceSelectedIncidentFaces S e).Nonempty := by
  classical
  simp [parafermionicCoverFiniteFaceSetEdgeSupport]

private theorem fillingContainment_no_three_incident {n : ℕ}
    (e : Sym2 (ParafermionicCoverBoxVertex n))
    (i j k : ParafermionicCoverFiniteFaceTopIndex n)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hi : e ∈ (parafermionicCoverFiniteFaceBoundaryGraph i.1 i.2).edgeSet)
    (hj : e ∈ (parafermionicCoverFiniteFaceBoundaryGraph j.1 j.2).edgeSet)
    (hk : e ∈ (parafermionicCoverFiniteFaceBoundaryGraph k.1 k.2).edgeSet) : False := by
  classical
  let I := parafermionicCoverFiniteFaceIncidentFaces e
  have hiI : i ∈ I := by
    simp only [I, parafermionicCoverFiniteFaceIncidentFaces, Finset.mem_filter]
    exact ⟨Finset.mem_univ _,hi⟩
  have hjI : j ∈ I := by
    simp only [I, parafermionicCoverFiniteFaceIncidentFaces, Finset.mem_filter]
    exact ⟨Finset.mem_univ _,hj⟩
  have hkI : k ∈ I := by
    simp only [I, parafermionicCoverFiniteFaceIncidentFaces, Finset.mem_filter]
    exact ⟨Finset.mem_univ _,hk⟩
  have hsub : ({i,j,k} : Finset (ParafermionicCoverFiniteFaceTopIndex n)) ⊆ I := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl
    · exact hiI
    · exact hjI
    · exact hkI
  have hthree : ({i,j,k} : Finset (ParafermionicCoverFiniteFaceTopIndex n)).card = 3 := by
    simp [hij,hik,hjk]
  have hcard := Finset.card_le_card hsub
  have hbound := parafermionicCoverFiniteFaceIncidentFaces_card_le_two e
  dsimp [I] at hcard hbound
  omega

private theorem fillingContainment_crossEdge_card_one {n : ℕ}
    (T : Finset (ParafermionicCoverFiniteFaceTopIndex n))
    (i j : ParafermionicCoverFiniteFaceTopIndex n)
    (e : Sym2 (ParafermionicCoverBoxVertex n)) (hij : i ≠ j)
    (hiEdge : e ∈ (parafermionicCoverFiniteFaceBoundaryGraph i.1 i.2).edgeSet)
    (hjEdge : e ∈ (parafermionicCoverFiniteFaceBoundaryGraph j.1 j.2).edgeSet)
    (hiT : i ∈ T) (hjT : j ∉ T) :
    (parafermionicCoverFiniteFaceSelectedIncidentFaces T e).card = 1 := by
  classical
  have hiSelected : i ∈ parafermionicCoverFiniteFaceSelectedIncidentFaces T e :=
    (fillingContainment_selectedIncident_mem T e i).2 ⟨hiT, hiEdge⟩
  have hle : (parafermionicCoverFiniteFaceSelectedIncidentFaces T e).card ≤ 1 :=
    Finset.card_le_one.mpr (by
      intro a ha b hb
      have haData := (fillingContainment_selectedIncident_mem T e a).mp ha
      have hbData := (fillingContainment_selectedIncident_mem T e b).mp hb
      have haEq : a = i := by
        by_contra hneai
        have hja : j ≠ a := by
          intro heq
          subst a
          exact hjT haData.1
        exact fillingContainment_no_three_incident e i j a hij (Ne.symm hneai) hja
          hiEdge hjEdge haData.2
      have hbEq : b = i := by
        by_contra hnebi
        have hjb : j ≠ b := by
          intro heq
          subst b
          exact hjT hbData.1
        exact fillingContainment_no_three_incident e i j b hij (Ne.symm hnebi) hjb
          hiEdge hjEdge hbData.2
      exact haEq.trans hbEq.symm)
  have hpos : 0 < (parafermionicCoverFiniteFaceSelectedIncidentFaces T e).card :=
    Finset.card_pos.mpr ⟨i, hiSelected⟩
  omega

private theorem fillingContainment_exposed_not_mem {n : ℕ}
    (S T : Finset (ParafermionicCoverFiniteFaceTopIndex n))
    (hsub : (parafermionicCoverFiniteFaceSetBoundaryGraph T).edgeSet ⊆
      (parafermionicCoverFiniteFaceSetEdgeSupport S : Set (Sym2 (ParafermionicCoverBoxVertex n))))
    (i : ParafermionicCoverFiniteFaceTopIndex n) (hiS : i ∉ S)
    (e : Sym2 (ParafermionicCoverBoxVertex n))
    (hiEdge : e ∈ (parafermionicCoverFiniteFaceBoundaryGraph i.1 i.2).edgeSet)
    (hexposed : ∀ j, j ≠ i → e ∉
      (parafermionicCoverFiniteFaceBoundaryGraph j.1 j.2).edgeSet) :
    i ∉ T := by
  intro hiT
  have hcard : (parafermionicCoverFiniteFaceSelectedIncidentFaces T e).card = 1 := by
    have hle : (parafermionicCoverFiniteFaceSelectedIncidentFaces T e).card ≤ 1 :=
      Finset.card_le_one.mpr (by
        intro a ha b hb
        have haData := (fillingContainment_selectedIncident_mem T e a).mp ha
        have hbData := (fillingContainment_selectedIncident_mem T e b).mp hb
        have haEq : a = i := by
          by_contra hneai
          exact hexposed a hneai haData.2
        have hbEq : b = i := by
          by_contra hnebi
          exact hexposed b hnebi hbData.2
        exact haEq.trans hbEq.symm)
    have hpos : 0 < (parafermionicCoverFiniteFaceSelectedIncidentFaces T e).card :=
      Finset.card_pos.mpr ⟨i, (fillingContainment_selectedIncident_mem T e i).2 ⟨hiT,hiEdge⟩⟩
    omega
  have hTedge :=
    (parafermionicCoverFiniteFaceSetBoundaryGraph_edge_iff_selectedIncidentFaces_card_eq_one
      T e).2 hcard
  have hsupp := hsub hTedge
  obtain ⟨k,hk⟩ := (fillingContainment_support_mem_iff S e).mp hsupp
  obtain ⟨hkS,hkEdge⟩ := (fillingContainment_selectedIncident_mem S e k).mp hk
  have hki : k ≠ i := by
    intro heq
    subst k
    exact hiS hkS
  exact (hexposed k hki hkEdge).elim

private theorem fillingContainment_crossEdge_forces_both_or_neither {n : ℕ}
    (S T : Finset (ParafermionicCoverFiniteFaceTopIndex n))
    (hsub : (parafermionicCoverFiniteFaceSetBoundaryGraph T).edgeSet ⊆
      (parafermionicCoverFiniteFaceSetEdgeSupport S : Set (Sym2 (ParafermionicCoverBoxVertex n))))
    (i j : ParafermionicCoverFiniteFaceTopIndex n)
    (hiS : i ∉ S) (hjS : j ∉ S)
    (hij : (parafermionicCoverFiniteFaceAdjacencyGraph n).Adj i j) :
    i ∈ T ↔ j ∈ T := by
  classical
  rcases hij with ⟨hne, e, hiEdge, hjEdge⟩
  constructor
  · intro hiT
    by_contra hjT
    have hcard := fillingContainment_crossEdge_card_one T i j e hne hiEdge hjEdge hiT hjT
    have hTedge :=
      (parafermionicCoverFiniteFaceSetBoundaryGraph_edge_iff_selectedIncidentFaces_card_eq_one
        T e).2 hcard
    obtain ⟨k, hk⟩ := (fillingContainment_support_mem_iff S e).mp (hsub hTedge)
    obtain ⟨hkS, hkEdge⟩ := (fillingContainment_selectedIncident_mem S e k).mp hk
    have hki : k ≠ i := by intro heq; subst k; exact hiS hkS
    have hkj : j ≠ k := by
      intro heq
      subst k
      exact hjS hkS
    exact fillingContainment_no_three_incident e i j k hne hki.symm hkj hiEdge hjEdge hkEdge
  · intro hjT
    by_contra hiT
    have hcard := fillingContainment_crossEdge_card_one T j i e hne.symm hjEdge hiEdge hjT hiT
    have hTedge :=
      (parafermionicCoverFiniteFaceSetBoundaryGraph_edge_iff_selectedIncidentFaces_card_eq_one
        T e).2 hcard
    obtain ⟨k, hk⟩ := (fillingContainment_support_mem_iff S e).mp (hsub hTedge)
    obtain ⟨hkS, hkEdge⟩ := (fillingContainment_selectedIncident_mem S e k).mp hk
    have hkj : k ≠ j := by intro heq; subst k; exact hjS hkS
    have hik : i ≠ k := by
      intro heq
      subst k
      exact hiS hkS
    exact fillingContainment_no_three_incident e j i k hne.symm hkj.symm hik hjEdge hiEdge hkEdge

/-- If the symmetric-difference boundary of a finite actual face family uses
only edges in a fixed cycle filling's actual face support, then every face in
the family belongs to that filling. -/
theorem parafermionicCoverSimpleCycleFillingSet_contains_boundary_supported_faces
    {n : ℕ} (hn : 1 ≤ n) {u : ParafermionicCoverBoxVertex n}
    (p : (parafermionicCoverBoxGraph n).Walk u u) (hp : p.IsCycle)
    (T : Finset (ParafermionicCoverFiniteFaceTopIndex n))
    (hsub : (parafermionicCoverFiniteFaceSetBoundaryGraph T).edgeSet ⊆
      (parafermionicCoverFiniteFaceSetEdgeSupport
        (parafermionicCoverSimpleCycleFillingSet hn p hp) :
          Set (Sym2 (ParafermionicCoverBoxVertex n)))) :
    T ⊆ parafermionicCoverSimpleCycleFillingSet hn p hp := by
  classical
  let S := parafermionicCoverSimpleCycleFillingSet hn p hp
  let Cset := parafermionicCoverSimpleCycleComplementCarrier S
  let G : SimpleGraph (Option (ParafermionicCoverFiniteFaceTopIndex n)) :=
    parafermionicCoverFiniteFaceAdjacencyWithBoundaryGraph n
  let C : SimpleGraph Cset := G.induce Cset
  let root : Cset := ⟨none, by simp [Cset, parafermionicCoverSimpleCycleComplementCarrier]⟩
  have hconnected := parafermionicCoverSimpleCycleComplementAdjacency_connected hn p hp
  have hreachable : ∀ y : Cset, C.Reachable root y := by
    intro y
    have hc := hconnected.preconnected root y
    exact hc
  intro i hiT
  by_contra hiS
  let vi : Cset := ⟨some i, by
    change i ∉ S
    simpa [S] using hiS⟩
  obtain ⟨walk⟩ := hreachable vi
  let P : Cset → Prop := fun x => x.1.elim False (fun j => j ∈ T)
  have hboundaryStable : ∀ {x y : Cset}, (w : C.Walk x y) → (P x ↔ P y) := by
    intro x y w
    induction w with
    | nil => simp
    | @cons x y z hadj tail ih =>
        have hstep : P x ↔ P y := by
          change G.Adj x.1 y.1 at hadj
          cases hx : x.1 with
          | none =>
            cases hy : y.1 with
            | none =>
              have hadj' :
                  (parafermionicCoverFiniteFaceAdjacencyWithBoundaryGraph n).Adj none none := by
                simp [G, hx, hy] at hadj
              change False at hadj'
              exact hadj'.elim
            | some j =>
              obtain ⟨e, hjEdge, hexposed⟩ :=
                (parafermionicCoverFiniteFaceAdjacencyWithBoundaryGraph_adj_none_some_iff j).mp
                  (by simpa [G, hx, hy] using hadj)
              have hjS : j ∉ S := by
                simpa [Cset, parafermionicCoverSimpleCycleComplementCarrier, hy] using y.2
              have hjT := fillingContainment_exposed_not_mem S T hsub j hjS e hjEdge hexposed
              simp [P, hx, hy, hjT]
          | some i =>
            cases hy : y.1 with
            | none =>
              have hadj' : ∃ e, e ∈ (parafermionicCoverFiniteFaceBoundaryGraph i.1 i.2).edgeSet ∧
                  ∀ j, j ≠ i → e ∉ (parafermionicCoverFiniteFaceBoundaryGraph j.1 j.2).edgeSet := by
                simpa [G, hx, hy, parafermionicCoverFiniteFaceAdjacencyWithBoundaryGraph] using hadj
              obtain ⟨e, hiEdge, hexposed⟩ := hadj'
              have hiS : i ∉ S := by
                simpa [Cset, parafermionicCoverSimpleCycleComplementCarrier, hx] using x.2
              have hiT := fillingContainment_exposed_not_mem S T hsub i hiS e hiEdge hexposed
              simp [P, hx, hy, hiT]
            | some j =>
              have hiS : i ∉ S := by
                simpa [Cset, parafermionicCoverSimpleCycleComplementCarrier, hx] using x.2
              have hjS : j ∉ S := by
                simpa [Cset, parafermionicCoverSimpleCycleComplementCarrier, hy] using y.2
              have hadj' := (parafermionicCoverFiniteFaceAdjacencyWithBoundaryGraph_adj_some_some_iff i j).mp
                (by simpa [G, hx, hy] using hadj)
              have hmem := fillingContainment_crossEdge_forces_both_or_neither
                S T hsub i j hiS hjS hadj'
              simpa [P, hx, hy] using hmem
        exact hstep.trans ih
  have hroot : ¬ P root := by simp [P, root]
  have hfinal := hboundaryStable walk
  have hend : P vi := by simpa [P, vi] using hiT
  have hstart : P root := hfinal.mpr hend
  exact hroot hstart

end PottsDiscontinuity.TorusTopology.Planar.Medial
