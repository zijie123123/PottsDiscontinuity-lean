/- Adapted from an earlier, unpublished formalization of the planar FK model by the same author.
Adaptation: Namespace and import relocation only. -/
module

public import Mathlib.Tactic
public import PottsDiscontinuity.TorusTopology.PlanarParafermionicCoverFaceOrientedBoundary

@[expose] public section

namespace PottsDiscontinuity.TorusTopology.Planar.Medial

open PottsDiscontinuity.TorusTopology.Planar

def coverFaceDartList (f : ParafermionicCoverVertex) :
    List (ParafermionicCoverVertex × ParafermionicCoverVertex) :=
  [(f, parafermionicCoverFaceRightLift f.1.1 f.1.2 f.2),
   (parafermionicCoverFaceRightLift f.1.1 f.1.2 f.2,
     parafermionicCoverFaceRightUpLift f.1.1 f.1.2 f.2),
   (parafermionicCoverFaceRightUpLift f.1.1 f.1.2 f.2,
     parafermionicCoverFaceRightUpLeftLift f.1.1 f.1.2 f.2),
   (parafermionicCoverFaceRightUpLeftLift f.1.1 f.1.2 f.2, f)]

private theorem coverFaceVertices_nodup (f : ParafermionicCoverVertex) :
    [f, parafermionicCoverFaceRightLift f.1.1 f.1.2 f.2,
      parafermionicCoverFaceRightUpLift f.1.1 f.1.2 f.2,
      parafermionicCoverFaceRightUpLeftLift f.1.1 f.1.2 f.2].Nodup := by
  rcases f with ⟨⟨x,y⟩,k⟩
  simp only [List.nodup_cons, List.mem_cons]
  repeat' constructor <;> simp [parafermionicCoverFaceRightLift_formula,
    parafermionicCoverFaceRightUpLift_formula,
    parafermionicCoverFaceRightUpLeftLift_formula]

private theorem coverFaceDartList_nodup (f : ParafermionicCoverVertex) :
    (coverFaceDartList f).Nodup := by
  rcases f with ⟨⟨x,y⟩,k⟩
  have hv := coverFaceVertices_nodup ((⟨(x,y),k⟩ : ParafermionicCoverVertex))
  simp only [coverFaceDartList, List.nodup_cons, List.mem_cons]
  repeat' constructor <;> simp [parafermionicCoverFaceRightLift_formula,
    parafermionicCoverFaceRightUpLift_formula,
    parafermionicCoverFaceRightUpLeftLift_formula]

private theorem coverFaceDartList_toFinset (f : ParafermionicCoverVertex) :
    (coverFaceDartList f).toFinset = parafermionicCoverFiniteFaceDarts f := by
  ext d
  simp [coverFaceDartList, parafermionicCoverFiniteFaceDarts]

private theorem sum_outgoing_dart_indicator {n : ℕ}
    (D : Finset (ParafermionicCoverVertex × ParafermionicCoverVertex))
    (hend : ∀ d ∈ D, d.2 ∈ parafermionicCoverBoxVertices n)
    (u : ParafermionicCoverBoxVertex n) :
    (∑ v : ParafermionicCoverBoxVertex n,
      if (u.1,v.1) ∈ D then (1 : ℤ) else 0) =
      ∑ d ∈ D, if d.1 = u.1 then (1 : ℤ) else 0 := by
  classical
  calc
    (∑ v : ParafermionicCoverBoxVertex n,
      if (u.1,v.1) ∈ D then (1 : ℤ) else 0) =
        ∑ v : ParafermionicCoverBoxVertex n,
          ∑ d ∈ D, if d = (u.1,v.1) then (1 : ℤ) else 0 := by
      apply Finset.sum_congr rfl
      intro v hv
      rw [Finset.sum_ite_eq']
    _ = ∑ d ∈ D, ∑ v : ParafermionicCoverBoxVertex n,
        if d = (u.1,v.1) then (1 : ℤ) else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ d ∈ D, if d.1 = u.1 then (1 : ℤ) else 0 := by
      apply Finset.sum_congr rfl
      intro d hd
      let w : ParafermionicCoverBoxVertex n := ⟨d.2, hend d hd⟩
      by_cases hsource : d.1 = u.1
      · rw [Finset.sum_eq_single w]
        · have hselected : d = (u.1,w.1) := by
            exact Prod.ext hsource rfl
          simp [hselected]
        · intro v hv hvne
          have hpair : d ≠ (u.1,v.1) := by
            intro heq
            apply hvne
            apply Subtype.ext
            exact (congrArg Prod.snd heq).symm
          simp [hpair]
        · simp
      · rw [Finset.sum_eq_zero]
        · simp [hsource]
        · intro v hv
          have hpair : d ≠ (u.1,v.1) := by
            intro heq
            exact hsource (congrArg Prod.fst heq)
          simp [hpair]

private theorem sum_incoming_dart_indicator {n : ℕ}
    (D : Finset (ParafermionicCoverVertex × ParafermionicCoverVertex))
    (hstart : ∀ d ∈ D, d.1 ∈ parafermionicCoverBoxVertices n)
    (u : ParafermionicCoverBoxVertex n) :
    (∑ v : ParafermionicCoverBoxVertex n,
      if (v.1,u.1) ∈ D then (1 : ℤ) else 0) =
      ∑ d ∈ D, if d.2 = u.1 then (1 : ℤ) else 0 := by
  classical
  calc
    (∑ v : ParafermionicCoverBoxVertex n,
      if (v.1,u.1) ∈ D then (1 : ℤ) else 0) =
        ∑ v : ParafermionicCoverBoxVertex n,
          ∑ d ∈ D, if d = (v.1,u.1) then (1 : ℤ) else 0 := by
      apply Finset.sum_congr rfl
      intro v hv
      rw [Finset.sum_ite_eq']
    _ = ∑ d ∈ D, ∑ v : ParafermionicCoverBoxVertex n,
        if d = (v.1,u.1) then (1 : ℤ) else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ d ∈ D, if d.2 = u.1 then (1 : ℤ) else 0 := by
      apply Finset.sum_congr rfl
      intro d hd
      let w : ParafermionicCoverBoxVertex n := ⟨d.1, hstart d hd⟩
      by_cases htarget : d.2 = u.1
      · rw [Finset.sum_eq_single w]
        · have hselected : d = (w.1,u.1) := by exact Prod.ext rfl htarget
          simp [hselected]
        · intro v hv hvne
          have hpair : d ≠ (v.1,u.1) := by
            intro heq
            apply hvne
            apply Subtype.ext
            exact (congrArg Prod.fst heq).symm
          simp [hpair]
        · simp
      · rw [Finset.sum_eq_zero]
        · simp [htarget]
        · intro v hv
          have hpair : d ≠ (v.1,u.1) := by
            intro heq
            exact htarget (congrArg Prod.snd heq)
          simp [hpair]

private theorem coverFaceDartSourceSum_eq_targetSum (f : ParafermionicCoverVertex)
    (u : ParafermionicCoverVertex) :
    (∑ d ∈ parafermionicCoverFiniteFaceDarts f,
      if d.1 = u then (1 : ℤ) else 0) =
    ∑ d ∈ parafermionicCoverFiniteFaceDarts f,
      if d.2 = u then (1 : ℤ) else 0 := by
  classical
  rw [← coverFaceDartList_toFinset f]
  rw [List.sum_toFinset _ (coverFaceDartList_nodup f)]
  rw [List.sum_toFinset _ (coverFaceDartList_nodup f)]
  simp only [coverFaceDartList, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil]
  ring

private theorem coverFaceVertexDartDivergence {n : ℕ}
    (i : ParafermionicCoverFiniteFaceTopIndex n)
    (u : ParafermionicCoverBoxVertex n) :
    (∑ v : ParafermionicCoverBoxVertex n,
      if (u.1,v.1) ∈ parafermionicCoverFiniteFaceDarts i.1 then (1 : ℤ) else 0) =
    ∑ v : ParafermionicCoverBoxVertex n,
      if (v.1,u.1) ∈ parafermionicCoverFiniteFaceDarts i.1 then (1 : ℤ) else 0 := by
  rw [sum_outgoing_dart_indicator _ (fun d hd =>
    (parafermionicCoverFiniteFaceDart_endpoints_mem n i.1 i.2 hd).2) u]
  rw [sum_incoming_dart_indicator _ (fun d hd =>
    (parafermionicCoverFiniteFaceDart_endpoints_mem n i.1 i.2 hd).1) u]
  exact coverFaceDartSourceSum_eq_targetSum i.1 u.1

private theorem coverFacePositiveCount_eq_sum {n : ℕ}
    (S : Finset (ParafermionicCoverFiniteFaceTopIndex n))
    (u v : ParafermionicCoverBoxVertex n) :
    (parafermionicCoverFacePositiveDartCount S u v : ℤ) =
      ∑ i ∈ S, if (u.1,v.1) ∈ parafermionicCoverFiniteFaceDarts i.1 then 1 else 0 := by
  classical
  unfold parafermionicCoverFacePositiveDartCount
  rw [Finset.card_filter]
  norm_cast

theorem parafermionicCoverFaceBoundaryCoefficient_divergence {n : ℕ}
    (S : Finset (ParafermionicCoverFiniteFaceTopIndex n))
    (u : ParafermionicCoverBoxVertex n) :
    ∑ v : ParafermionicCoverBoxVertex n,
      parafermionicCoverFaceBoundaryCoefficient S u v = 0 := by
  classical
  unfold parafermionicCoverFaceBoundaryCoefficient
  rw [Finset.sum_sub_distrib]
  have hpos :
      (∑ v : ParafermionicCoverBoxVertex n,
        (parafermionicCoverFacePositiveDartCount S u v : ℤ)) =
        ∑ i ∈ S, ∑ v : ParafermionicCoverBoxVertex n,
          if (u.1,v.1) ∈ parafermionicCoverFiniteFaceDarts i.1 then (1 : ℤ) else 0 := by
    calc
      (∑ v : ParafermionicCoverBoxVertex n,
        (parafermionicCoverFacePositiveDartCount S u v : ℤ)) =
          ∑ v : ParafermionicCoverBoxVertex n, ∑ i ∈ S,
            if (u.1,v.1) ∈ parafermionicCoverFiniteFaceDarts i.1 then (1 : ℤ) else 0 := by
        apply Finset.sum_congr rfl
        intro v hv
        exact coverFacePositiveCount_eq_sum S u v
      _ = ∑ i ∈ S, ∑ v : ParafermionicCoverBoxVertex n,
          if (u.1,v.1) ∈ parafermionicCoverFiniteFaceDarts i.1 then (1 : ℤ) else 0 := by
        rw [Finset.sum_comm]
  have hneg :
      (∑ v : ParafermionicCoverBoxVertex n,
        (parafermionicCoverFacePositiveDartCount S v u : ℤ)) =
        ∑ i ∈ S, ∑ v : ParafermionicCoverBoxVertex n,
          if (v.1,u.1) ∈ parafermionicCoverFiniteFaceDarts i.1 then (1 : ℤ) else 0 := by
    calc
      (∑ v : ParafermionicCoverBoxVertex n,
        (parafermionicCoverFacePositiveDartCount S v u : ℤ)) =
          ∑ v : ParafermionicCoverBoxVertex n, ∑ i ∈ S,
            if (v.1,u.1) ∈ parafermionicCoverFiniteFaceDarts i.1 then (1 : ℤ) else 0 := by
        apply Finset.sum_congr rfl
        intro v hv
        exact coverFacePositiveCount_eq_sum S v u
      _ = ∑ i ∈ S, ∑ v : ParafermionicCoverBoxVertex n,
          if (v.1,u.1) ∈ parafermionicCoverFiniteFaceDarts i.1 then (1 : ℤ) else 0 := by
        rw [Finset.sum_comm]
  rw [hpos, hneg]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_eq_zero
  intro i hi
  exact sub_eq_zero.mpr (coverFaceVertexDartDivergence i u)

end PottsDiscontinuity.TorusTopology.Planar.Medial
