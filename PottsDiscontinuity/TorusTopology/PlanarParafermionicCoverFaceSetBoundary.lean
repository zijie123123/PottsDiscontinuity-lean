/- Adapted from an earlier, unpublished formalization of the planar FK model by the same author.
Adaptation: Namespace and import relocation only. -/
module

public import Mathlib.Tactic
public import PottsDiscontinuity.TorusTopology.PlanarParafermionicCoverFaceChainUniqueness
public import PottsDiscontinuity.TorusTopology.PlanarParafermionicCoverFaceOrientedBoundary

@[expose] public section

namespace PottsDiscontinuity.TorusTopology.Planar.Medial

open PottsDiscontinuity.TorusTopology.Planar
open SimpleGraph
open scoped symmDiff

@[instance_reducible] noncomputable def coverFaceSetLocallyFinite
    {V : Type*} [Fintype V] (G : SimpleGraph V) : LocallyFinite G := fun v =>
  Fintype.ofInjective (fun x : G.neighborSet v => x.1) Subtype.val_injective

private theorem faceSymmDiffList_even_degree {V I : Type*} [Fintype V]
    [DecidableEq V] (F : I → SimpleGraph V)
    (hF : ∀ i v, Even ((F i).neighborSet v).ncard) :
    ∀ L : List I, ∀ v, Even ((faceSymmDiffList F L).neighborSet v).ncard := by
  intro L
  induction L with
  | nil =>
    intro v
    let : LocallyFinite (faceSymmDiffList F []) :=
      coverFaceSetLocallyFinite (faceSymmDiffList F [])
    simp [faceSymmDiffList]
  | cons i L ih =>
    intro v
    let : LocallyFinite (F i) := coverFaceSetLocallyFinite (F i)
    let : LocallyFinite (faceSymmDiffList F L) :=
      coverFaceSetLocallyFinite (faceSymmDiffList F L)
    let : LocallyFinite (F i ∆ faceSymmDiffList F L) :=
      coverFaceSetLocallyFinite (F i ∆ faceSymmDiffList F L)
    have hFi : ∀ v, Even ((F i).degree v) := by
      intro w
      simpa only [SimpleGraph.ncard_neighborSet] using hF i w
    have htail : ∀ v, Even ((faceSymmDiffList F L).degree v) := by
      intro w
      simpa only [SimpleGraph.ncard_neighborSet] using ih w
    have hdegree := degree_even_symmDiff (F i) (faceSymmDiffList F L) hFi htail v
    change Even ((F i ∆ faceSymmDiffList F L).neighborSet v).ncard
    simpa only [SimpleGraph.ncard_neighborSet] using hdegree

noncomputable def parafermionicCoverFiniteFaceSetBoundaryGraph {n : ℕ}
    (S : Finset (ParafermionicCoverFiniteFaceTopIndex n)) :
    SimpleGraph (ParafermionicCoverBoxVertex n) :=
  faceSymmDiffList
    (fun i => parafermionicCoverFiniteFaceBoundaryGraph i.1 i.2) S.toList

theorem parafermionicCoverFiniteFaceSetBoundaryGraph_even_degree {n : ℕ}
    (S : Finset (ParafermionicCoverFiniteFaceTopIndex n)) :
    ∀ v : ParafermionicCoverBoxVertex n,
      Even ((parafermionicCoverFiniteFaceSetBoundaryGraph S).neighborSet v).ncard := by
  classical
  intro v
  let F : ParafermionicCoverFiniteFaceTopIndex n →
      SimpleGraph (ParafermionicCoverBoxVertex n) :=
    fun i => parafermionicCoverFiniteFaceBoundaryGraph i.1 i.2
  have hF : ∀ i v, Even ((F i).neighborSet v).ncard := by
    intro i v
    have he := parafermionicCoverFiniteFaceBoundaryGraph_even_degree i.1 i.2 v
    simpa only [F, parafermionicCoverFiniteFaceBoundaryDegree,
      SimpleGraph.ncard_neighborSet] using he
  have h := faceSymmDiffList_even_degree F hF S.toList v
  simpa only [parafermionicCoverFiniteFaceSetBoundaryGraph, F] using h

theorem parafermionicCoverFiniteFaceSetBoundaryGraph_eq_bot_iff {n : ℕ}
    (S : Finset (ParafermionicCoverFiniteFaceTopIndex n)) :
    parafermionicCoverFiniteFaceSetBoundaryGraph S = ⊥ ↔ S = ∅ := by
  classical
  constructor
  · intro h
    have hEq : faceSymmDiffList
        (fun i : ParafermionicCoverFiniteFaceTopIndex n =>
          parafermionicCoverFiniteFaceBoundaryGraph i.1 i.2) S.toList =
        faceSymmDiffList
          (fun i : ParafermionicCoverFiniteFaceTopIndex n =>
            parafermionicCoverFiniteFaceBoundaryGraph i.1 i.2) [] := by
      simpa [parafermionicCoverFiniteFaceSetBoundaryGraph, faceSymmDiffList] using h
    have hsets := parafermionicCoverFiniteFaceChain_toFinset_unique
      S.toList [] S.nodup_toList List.nodup_nil hEq
    rw [← Finset.toList_toFinset S]
    exact hsets
  · rintro rfl
    simp [parafermionicCoverFiniteFaceSetBoundaryGraph, faceSymmDiffList]

theorem parafermionicCoverFiniteFaceSetBoundaryGraph_ne_bot_iff {n : ℕ}
    (S : Finset (ParafermionicCoverFiniteFaceTopIndex n)) :
    parafermionicCoverFiniteFaceSetBoundaryGraph S ≠ ⊥ ↔ S.Nonempty := by
  constructor
  · intro hne
    have hsne : S ≠ ∅ := by
      intro hS
      apply hne
      exact (parafermionicCoverFiniteFaceSetBoundaryGraph_eq_bot_iff S).mpr hS
    exact Finset.nonempty_iff_ne_empty.mpr hsne
  · intro hS hbot
    have hEq := (parafermionicCoverFiniteFaceSetBoundaryGraph_eq_bot_iff S).mp hbot
    exact (Finset.nonempty_iff_ne_empty.mp hS) hEq

theorem parafermionicCoverFiniteFaceSetBoundaryGraph_coefficient_ne_zero_iff
    {n : ℕ} (S : Finset (ParafermionicCoverFiniteFaceTopIndex n))
    (u v : ParafermionicCoverBoxVertex n) :
    parafermionicCoverFaceBoundaryCoefficient S u v ≠ 0 ↔
      s(u,v) ∈ (parafermionicCoverFiniteFaceSetBoundaryGraph S).edgeSet := by
  classical
  unfold parafermionicCoverFiniteFaceSetBoundaryGraph
  exact parafermionicCoverFaceBoundaryCoefficient_ne_zero_iff
    S S.toList S.nodup_toList (by simp) u v

end PottsDiscontinuity.TorusTopology.Planar.Medial
