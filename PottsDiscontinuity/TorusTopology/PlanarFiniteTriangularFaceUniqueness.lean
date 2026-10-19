/- Adapted from an earlier, unpublished formalization of the planar FK model by the same author.
Adaptation: Namespace and import relocation only. -/
module

public import PottsDiscontinuity.TorusTopology.PlanarFiniteTriangularFaceIndependence
public import Mathlib.Tactic

@[expose] public section

namespace PottsDiscontinuity.TorusTopology.Planar.Medial

open SimpleGraph
open scoped symmDiff

theorem faceSymmDiffList_eq_implies_toFinset_eq
    {V I : Type*} [DecidableEq I]
    (F : I → SimpleGraph V) (p : I → Sym2 V) (rank : I → ℕ)
    (hpF : ∀ i, p i ∈ (F i).edgeSet)
    (htri : ∀ i j, p j ∈ (F i).edgeSet → j = i ∨ rank j < rank i)
    (L M : List I) (hLnodup : L.Nodup) (hMnodup : M.Nodup)
    (hEq : faceSymmDiffList F L = faceSymmDiffList F M) :
    L.toFinset = M.toFinset := by
  classical
  by_contra hLM
  let D := L.toFinset ∆ M.toFinset
  have hDne : D.Nonempty := by
    exact Finset.symmDiff_nonempty.mpr hLM
  obtain ⟨f, hfD, hmax⟩ := D.exists_max_image rank hDne
  have hcommon : ∀ i, rank f < rank i →
      (i ∈ L.toFinset ↔ i ∈ M.toFinset) := by
    intro i hri
    constructor
    · intro hiL
      by_contra hiM
      have hiD : i ∈ D := by
        change i ∈ L.toFinset ∆ M.toFinset
        rw [Finset.mem_symmDiff]
        exact Or.inl ⟨hiL, hiM⟩
      have hbound := hmax i hiD
      omega
    · intro hiM
      by_contra hiL
      have hiD : i ∈ D := by
        change i ∈ L.toFinset ∆ M.toFinset
        rw [Finset.mem_symmDiff]
        exact Or.inr ⟨hiM, hiL⟩
      have hbound := hmax i hiD
      omega
  let P : I → Prop := fun i => p f ∈ (F i).edgeSet
  let CL : Finset I := L.toFinset.filter P
  let CM : Finset I := M.toFinset.filter P
  have herase : CL.erase f = CM.erase f := by
    ext i
    change i ∈ (L.toFinset.filter P).erase f ↔ i ∈ (M.toFinset.filter P).erase f
    simp only [Finset.mem_erase, Finset.mem_filter, P]
    constructor
    · intro hi
      have hne := hi.1
      have hiL := hi.2.1
      have hPi := hi.2.2
      have hri : rank f < rank i := by
        rcases htri i f hPi with hEq | hlt
        · exact (hne hEq.symm).elim
        · exact hlt
      exact ⟨hne, (hcommon i hri).mp hiL, hPi⟩
    · intro hi
      have hne := hi.1
      have hiM := hi.2.1
      have hPi := hi.2.2
      have hri : rank f < rank i := by
        rcases htri i f hPi with hEq | hlt
        · exact (hne hEq.symm).elim
        · exact hlt
      exact ⟨hne, (hcommon i hri).mpr hiM, hPi⟩
  have hcountL : L.countP (fun i => p f ∈ (F i).edgeSet) = CL.card := by
    exact (List.Nodup.card_eq_countP hLnodup).symm
  have hcountM : M.countP (fun i => p f ∈ (F i).edgeSet) = CM.card := by
    exact (List.Nodup.card_eq_countP hMnodup).symm
  have hmod :
      (L.countP (fun i => p f ∈ (F i).edgeSet) % 2 = 1) ↔
      (M.countP (fun i => p f ∈ (F i).edgeSet) % 2 = 1) := by
    have hparL := faceSymmDiffList_edge_iff_countP_mod F L (p f)
    have hparM := faceSymmDiffList_edge_iff_countP_mod F M (p f)
    have hEdge : p f ∈ (faceSymmDiffList F L).edgeSet ↔
        p f ∈ (faceSymmDiffList F M).edgeSet := by rw [hEq]
    exact hparL.symm.trans (hEdge.trans hparM)
  rcases Finset.mem_symmDiff.mp hfD with ⟨hfL, hfM⟩ | ⟨hfM, hfL⟩
  · have hpf : p f ∈ (F f).edgeSet := hpF f
    have hfCL : f ∈ CL := Finset.mem_filter.mpr ⟨hfL,hpf⟩
    have hfCM : f ∉ CM := by
      intro h
      exact hfM (Finset.mem_filter.mp h).1
    have hcardL : CL.card = (CL.erase f).card + 1 := by
      have h := Finset.card_erase_add_one hfCL
      omega
    have hcardM : CM.card = (CM.erase f).card := by
      rw [Finset.erase_eq_of_notMem hfCM]
    rw [← herase] at hcardM
    have hplus : CL.card = CM.card + 1 := by omega
    rw [hcountL, hcountM] at hmod
    have hmL : (CL.card % 2 = 1) ↔ (CM.card % 2 = 1) := hmod
    omega
  · have hpf : p f ∈ (F f).edgeSet := hpF f
    have hfCM : f ∈ CM := Finset.mem_filter.mpr ⟨hfM,hpf⟩
    have hfCL : f ∉ CL := by
      intro h
      exact hfL (Finset.mem_filter.mp h).1
    have hcardM : CM.card = (CM.erase f).card + 1 := by
      have h := Finset.card_erase_add_one hfCM
      omega
    have hcardL : CL.card = (CL.erase f).card := by
      rw [Finset.erase_eq_of_notMem hfCL]
    rw [← herase] at hcardM
    have hplus : CM.card = CL.card + 1 := by omega
    rw [hcountL, hcountM] at hmod
    have hmL : (CL.card % 2 = 1) ↔ (CM.card % 2 = 1) := hmod
    omega

end PottsDiscontinuity.TorusTopology.Planar.Medial
