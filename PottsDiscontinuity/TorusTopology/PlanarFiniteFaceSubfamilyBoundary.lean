/- Adapted from an earlier, unpublished formalization of the planar FK model by the same author.
Adaptation: Namespace and import relocation only. -/
module

public import PottsDiscontinuity.TorusTopology.PlanarFiniteTriangularFaceIndependence
public import Mathlib.Tactic

@[expose] public section

namespace PottsDiscontinuity.TorusTopology.Planar.Medial

open SimpleGraph
open scoped symmDiff

/-- If a selected face family has no edge in common with any omitted face,
every edge in its symmetric-difference boundary remains in the larger family's
boundary. -/
theorem faceSymmDiffList_edge_mem_mono_of_no_cross_shared_edge
    {V I : Type*} [DecidableEq I] (F : I → SimpleGraph V)
    (T S : Finset I) (hTS : T ⊆ S)
    (hcross : ∀ i ∈ T, ∀ j ∈ S, j ∉ T →
      Disjoint (F i).edgeSet (F j).edgeSet)
    (e : Sym2 V) :
    e ∈ (faceSymmDiffList F T.toList).edgeSet →
      e ∈ (faceSymmDiffList F S.toList).edgeSet := by
  classical
  let D := S \ T
  let p : I → Bool := fun i => decide (e ∈ (F i).edgeSet)
  have hparT := faceSymmDiffList_edge_iff_countP_mod F T.toList e
  have hparS := faceSymmDiffList_edge_iff_countP_mod F S.toList e
  intro heT
  have hcountT : (T.toList.countP p) % 2 = 1 := by
    exact hparT.mp heT
  have hpositive : 0 < T.toList.countP p := by omega
  have hfilterpositive : 0 < (T.toList.filter p).length := by
    simpa [List.countP_eq_length_filter] using hpositive
  obtain ⟨i, rest, hfilter⟩ : ∃ i rest, T.toList.filter p = i :: rest := by
    cases h : T.toList.filter p with
    | nil => simp [h] at hfilterpositive
    | cons i rest => exact ⟨i, rest, rfl⟩
  have hiFilter : i ∈ T.toList.filter p := by simp [hfilter]
  have hiParts := List.mem_filter.mp hiFilter
  have hiT : i ∈ T := Finset.mem_toList.mp hiParts.1
  have hie : e ∈ (F i).edgeSet := of_decide_eq_true hiParts.2
  have hnotD : ∀ j ∈ D.toList, e ∉ (F j).edgeSet := by
    intro j hj hje
    have hjD : j ∈ S \ T := by
      simpa [D] using Finset.mem_toList.mp hj
    rcases Finset.mem_sdiff.mp hjD with ⟨hjS, hjnotT⟩
    exact (Set.disjoint_left.mp (hcross i hiT j hjS hjnotT)) hie hje
  have hfalseD : ∀ j ∈ D.toList, p j = false := by
    intro j hj
    cases hpj : p j with
    | false => rfl
    | true => exact (hnotD j hj (of_decide_eq_true hpj)).elim
  have hcountD : D.toList.countP p = 0 := by
    rw [List.countP_eq_length_filter]
    have hfilterD : D.toList.filter p = [] := by
      apply List.filter_eq_nil_iff.mpr
      intro j hj
      simp [hfalseD j hj]
    rw [hfilterD]
    rfl
  have hdisjoint : List.Disjoint T.toList D.toList := by
    rw [List.disjoint_left]
    intro j hjT hjD
    have hjFin : j ∈ D := Finset.mem_toList.mp hjD
    have hjSDiff : j ∈ S \ T := by simpa [D] using hjFin
    exact (Finset.mem_sdiff.mp hjSDiff).2 (Finset.mem_toList.mp hjT)
  have hnodup : (T.toList ++ D.toList).Nodup :=
    List.Nodup.append T.nodup_toList D.nodup_toList hdisjoint
  have htoFinset : (T.toList ++ D.toList).toFinset = S := by
    simpa [List.toFinset_append, D] using Finset.union_sdiff_of_subset hTS
  have hfin : S.toList.toFinset = (T.toList ++ D.toList).toFinset := by
    calc
      S.toList.toFinset = S := Finset.toList_toFinset _
      _ = (T.toList ++ D.toList).toFinset := htoFinset.symm
  have hperm : List.Perm S.toList (T.toList ++ D.toList) :=
    List.perm_of_nodup_nodup_toFinset_eq S.nodup_toList hnodup hfin
  have hcountS : S.toList.countP p = T.toList.countP p := by
    calc
      S.toList.countP p = (T.toList ++ D.toList).countP p := hperm.countP_eq p
      _ = T.toList.countP p := by
        rw [List.countP_append, hcountD]
        simp
  have hcountSmod : (S.toList.countP p) % 2 = 1 := by
    rw [hcountS]
    exact hcountT
  exact hparS.mpr hcountSmod

/-- The graph symmetric-difference boundary of a selected subfamily is contained
in that of the full family when no selected face shares an edge with an omitted
face. -/
theorem faceSymmDiffList_le_of_no_cross_shared_edge
    {V I : Type*} [DecidableEq I] (F : I → SimpleGraph V)
    (T S : Finset I) (hTS : T ⊆ S)
    (hcross : ∀ i ∈ T, ∀ j ∈ S, j ∉ T →
      Disjoint (F i).edgeSet (F j).edgeSet) :
    faceSymmDiffList F T.toList ≤ faceSymmDiffList F S.toList := by
  intro u v huv
  apply (faceSymmDiffList F S.toList).mem_edgeSet.mp
  apply faceSymmDiffList_edge_mem_mono_of_no_cross_shared_edge F T S hTS hcross
  exact (faceSymmDiffList F T.toList).mem_edgeSet.mpr huv

end PottsDiscontinuity.TorusTopology.Planar.Medial
