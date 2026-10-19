/- Adapted from an earlier, unpublished formalization of the planar FK model by the same author.
Adaptation: Namespace and import relocation only. -/
module

public import Mathlib.Tactic
public import PottsDiscontinuity.TorusTopology.PlanarParafermionicCoverFaceAdjacency
public import PottsDiscontinuity.TorusTopology.PlanarParafermionicCoverSelectedFaceIncidence

@[expose] public section

namespace PottsDiscontinuity.TorusTopology.Planar.Medial

open PottsDiscontinuity.TorusTopology.Planar

private theorem coverFaceSetPositiveDartCount_le_one {n : ℕ}
    (S : Finset (ParafermionicCoverFiniteFaceTopIndex n))
    (u v : ParafermionicCoverBoxVertex n) :
    parafermionicCoverFacePositiveDartCount S u v ≤ 1 := by
  classical
  unfold parafermionicCoverFacePositiveDartCount
  apply Finset.card_le_one.mpr
  intro i hi j hj
  have hdi : (u.1,v.1) ∈ parafermionicCoverFiniteFaceDarts i.1 :=
    (Finset.mem_filter.mp hi).2
  have hdj : (u.1,v.1) ∈ parafermionicCoverFiniteFaceDarts j.1 :=
    (Finset.mem_filter.mp hj).2
  have hfaces := parafermionicCoverFiniteFaceDart_unique n i.2 j.2 hdi hdj
  exact Subtype.ext hfaces

private theorem coverFaceSetDarts_no_opposite {f : ParafermionicCoverVertex}
    {u v : ParafermionicCoverVertex}
    (huv : (u,v) ∈ parafermionicCoverFiniteFaceDarts f)
    (hvu : (v,u) ∈ parafermionicCoverFiniteFaceDarts f) : False := by
  rcases f with ⟨⟨x,y⟩,k⟩
  simp only [parafermionicCoverFiniteFaceDarts, Finset.mem_insert,
    Finset.mem_singleton, parafermionicCoverFaceRightLift_formula,
    parafermionicCoverFaceRightUpLift_formula,
    parafermionicCoverFaceRightUpLeftLift_formula] at huv hvu
  rcases huv with h1 | h2 | h3 | h4 <;>
    rcases hvu with h1' | h2' | h3' | h4' <;>
    simp_all

private theorem coverFaceSet_exists_dart {n : ℕ}
    (S : Finset (ParafermionicCoverFiniteFaceTopIndex n))
    (u v : ParafermionicCoverBoxVertex n)
    (hcount : parafermionicCoverFacePositiveDartCount S u v = 1) :
    ∃ i, i ∈ S ∧ (u.1,v.1) ∈ parafermionicCoverFiniteFaceDarts i.1 := by
  classical
  have hpos : 0 < parafermionicCoverFacePositiveDartCount S u v := by omega
  unfold parafermionicCoverFacePositiveDartCount at hpos
  obtain ⟨i, hi⟩ := Finset.card_pos.mp hpos
  exact ⟨i, (Finset.mem_filter.mp hi).1, (Finset.mem_filter.mp hi).2⟩

private theorem coverFaceSet_not_three_incident {n : ℕ}
    (u v : ParafermionicCoverBoxVertex n)
    (i j k : ParafermionicCoverFiniteFaceTopIndex n)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hi : s(u,v) ∈ (parafermionicCoverFiniteFaceBoundaryGraph i.1 i.2).edgeSet)
    (hj : s(u,v) ∈ (parafermionicCoverFiniteFaceBoundaryGraph j.1 j.2).edgeSet)
    (hk : s(u,v) ∈ (parafermionicCoverFiniteFaceBoundaryGraph k.1 k.2).edgeSet) : False := by
  classical
  let I := parafermionicCoverFiniteFaceIncidentFaces (s(u,v))
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
    simp [hij, hik, hjk]
  have hcard := Finset.card_le_card hsub
  have hbound := parafermionicCoverFiniteFaceIncidentFaces_card_le_two (s(u,v))
  dsimp [I] at hcard hbound
  omega

/-- If a disjoint actual face family has no exposed edge and no shared edge
with the complement of both families, its actual boundary is contained in
the boundary of the selected family. -/
private theorem unselectedBoundary_coefficient_ne_zero {n : ℕ}
    (S T : Finset (ParafermionicCoverFiniteFaceTopIndex n))
    (hdisjoint : Disjoint S T)
    (hno_exposed : ∀ i ∈ T,
      ¬ (parafermionicCoverFiniteFaceAdjacencyWithBoundaryGraph n).Adj none (some i))
    (hno_cross : ∀ i ∈ T, ∀ j,
      j ∉ S → j ∉ T →
      ¬ (parafermionicCoverFiniteFaceAdjacencyGraph n).Adj i j)
    (u v : ParafermionicCoverBoxVertex n)
    (hp : parafermionicCoverFacePositiveDartCount T u v = 1)
    (hq : parafermionicCoverFacePositiveDartCount T v u = 0) :
    parafermionicCoverFaceBoundaryCoefficient S u v ≠ 0 := by
  classical
  have hST : Disjoint S T := hdisjoint
  obtain ⟨i, hiT, hidart⟩ := coverFaceSet_exists_dart T u v hp
  have hiEdge : s(u,v) ∈
      (parafermionicCoverFiniteFaceBoundaryGraph i.1 i.2).edgeSet :=
    (parafermionicCoverFiniteFaceBoundaryEdge_iff_darts i.1 i.2 u v).2 (Or.inl hidart)
  have hex : ∃ j, j ≠ i ∧ s(u,v) ∈
      (parafermionicCoverFiniteFaceBoundaryGraph j.1 j.2).edgeSet := by
    by_contra h
    have hall : ∀ j, j ≠ i → s(u,v) ∉
        (parafermionicCoverFiniteFaceBoundaryGraph j.1 j.2).edgeSet := by
      intro j hji hmem
      exact h ⟨j,hji,hmem⟩
    have hadj : (parafermionicCoverFiniteFaceAdjacencyWithBoundaryGraph n).Adj none (some i) :=
      (parafermionicCoverFiniteFaceAdjacencyWithBoundaryGraph_adj_none_some_iff i).2
        ⟨s(u,v),hiEdge,hall⟩
    exact (hno_exposed i hiT) hadj
  obtain ⟨j,hji,hjEdge⟩ := hex
  obtain ⟨a,b,hab_i,hba_j,hmap⟩ :=
    parafermionicCoverFiniteFaceBoundaryDistinctFaces_oppositeDarts i j hji.symm
      (s(u,v)) hiEdge hjEdge
  have hraw : s(u.1,v.1) = s(a,b) := by
    simpa [Sym2.map_mk] using hmap
  have hqj : (v.1,u.1) ∈ parafermionicCoverFiniteFaceDarts j.1 := by
    rcases Sym2.eq_iff.mp hraw with hsame | hrev
    · rcases hsame with ⟨rfl,rfl⟩
      exact hba_j
    · rcases hrev with ⟨rfl,rfl⟩
      exact (coverFaceSetDarts_no_opposite hidart hab_i).elim
  have hjnotT : j ∉ T := by
    intro hjT
    have hpos : 0 < parafermionicCoverFacePositiveDartCount T v u := by
      unfold parafermionicCoverFacePositiveDartCount
      apply Finset.card_pos.mpr
      refine ⟨j, Finset.mem_filter.mpr ⟨hjT,hqj⟩⟩
    have : parafermionicCoverFacePositiveDartCount T v u > 0 := by simpa using hpos
    omega
  have hjS : j ∈ S := by
    by_contra hjS
    have hadj : (parafermionicCoverFiniteFaceAdjacencyGraph n).Adj i j :=
      ⟨hji.symm, s(u,v), hiEdge, hjEdge⟩
    exact (hno_cross i hiT j hjS hjnotT) hadj
  have hPzero : parafermionicCoverFacePositiveDartCount S u v = 0 := by
    by_contra hP
    have hpos : 0 < parafermionicCoverFacePositiveDartCount S u v := by omega
    unfold parafermionicCoverFacePositiveDartCount at hpos
    obtain ⟨k,hk⟩ := Finset.card_pos.mp hpos
    have hkS := (Finset.mem_filter.mp hk).1
    have hkp := (Finset.mem_filter.mp hk).2
    have hki : k ≠ i := by
      intro hki
      subst k
      exact Finset.disjoint_left.mp hST hkS hiT
    have hkj : k ≠ j := by
      intro hkj
      subst k
      exact (coverFaceSetDarts_no_opposite hkp hqj).elim
    have hkEdge : s(u,v) ∈
        (parafermionicCoverFiniteFaceBoundaryGraph k.1 k.2).edgeSet :=
      (parafermionicCoverFiniteFaceBoundaryEdge_iff_darts k.1 k.2 u v).2 (Or.inl hkp)
    exact coverFaceSet_not_three_incident u v i j k hji.symm hki.symm hkj.symm
      hiEdge hjEdge hkEdge
  have hQone : parafermionicCoverFacePositiveDartCount S v u = 1 := by
    have hpos : 0 < parafermionicCoverFacePositiveDartCount S v u := by
      unfold parafermionicCoverFacePositiveDartCount
      apply Finset.card_pos.mpr
      exact ⟨j, Finset.mem_filter.mpr ⟨hjS,hqj⟩⟩
    have hle := coverFaceSetPositiveDartCount_le_one S v u
    omega
  unfold parafermionicCoverFaceBoundaryCoefficient
  rw [hPzero,hQone]
  norm_num

theorem parafermionicCoverFiniteFaceUnselectedBoundary_le_selectedBoundary
    {n : ℕ} (S T : Finset (ParafermionicCoverFiniteFaceTopIndex n))
    (hdisjoint : Disjoint S T)
    (hno_exposed : ∀ i ∈ T,
      ¬ (parafermionicCoverFiniteFaceAdjacencyWithBoundaryGraph n).Adj none (some i))
    (hno_cross : ∀ i ∈ T, ∀ j,
      j ∉ S → j ∉ T →
      ¬ (parafermionicCoverFiniteFaceAdjacencyGraph n).Adj i j) :
    parafermionicCoverFiniteFaceSetBoundaryGraph T ≤
      parafermionicCoverFiniteFaceSetBoundaryGraph S := by
  classical
  intro u v hTedge
  have hcoeffT : parafermionicCoverFaceBoundaryCoefficient T u v ≠ 0 :=
    (parafermionicCoverFiniteFaceSetBoundaryGraph_coefficient_ne_zero_iff T u v).2 hTedge
  let p := parafermionicCoverFacePositiveDartCount T u v
  let q := parafermionicCoverFacePositiveDartCount T v u
  have hp : p ≤ 1 := coverFaceSetPositiveDartCount_le_one T u v
  have hq : q ≤ 1 := coverFaceSetPositiveDartCount_le_one T v u
  have hcases : (p = 1 ∧ q = 0) ∨ (p = 0 ∧ q = 1) := by
    have hne : (p : ℤ) - q ≠ 0 := by
      simpa [p, q, parafermionicCoverFaceBoundaryCoefficient] using hcoeffT
    omega
  rcases hcases with ⟨hp1,hq0⟩ | ⟨hp0,hq1⟩
  · exact (parafermionicCoverFiniteFaceSetBoundaryGraph_coefficient_ne_zero_iff S u v).1
      (unselectedBoundary_coefficient_ne_zero S T hdisjoint hno_exposed hno_cross u v hp1 hq0)
  · have hrev := unselectedBoundary_coefficient_ne_zero S T hdisjoint hno_exposed hno_cross
      v u hq1 hp0
    have hanti := parafermionicCoverFaceBoundaryCoefficient_antisymm S u v
    have hcoeffS : parafermionicCoverFaceBoundaryCoefficient S u v ≠ 0 := by
      intro hz
      apply hrev
      have hn : -(parafermionicCoverFaceBoundaryCoefficient S v u) = 0 := by
        simpa [hz] using hanti
      exact neg_eq_zero.mp hn
    exact (parafermionicCoverFiniteFaceSetBoundaryGraph_coefficient_ne_zero_iff S u v).1 hcoeffS

end PottsDiscontinuity.TorusTopology.Planar.Medial
