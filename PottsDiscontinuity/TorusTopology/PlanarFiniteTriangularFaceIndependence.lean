/- Adapted from an earlier, unpublished formalization of the planar FK model by the same author.
Adaptation: Namespace and import relocation only. -/
module

public import PottsDiscontinuity.TorusTopology.PlanarFiniteEvenTriangularElimination
public import Mathlib.Tactic

@[expose] public section

namespace PottsDiscontinuity.TorusTopology.Planar.Medial

open SimpleGraph
open scoped symmDiff

theorem faceSymmDiffList_edge_iff_countP_mod {V I : Type*}
    [DecidableEq I] (F : I → SimpleGraph V) (L : List I) (e : Sym2 V)
    [DecidablePred (fun i => e ∈ (F i).edgeSet)] :
    e ∈ (faceSymmDiffList F L).edgeSet ↔
      (L.countP (fun i => decide (e ∈ (F i).edgeSet))) % 2 = 1 := by
  classical
  induction L with
  | nil => simp [faceSymmDiffList]
  | cons i L ih =>
      by_cases h : e ∈ (F i).edgeSet
      · simp [faceSymmDiffList, symmDiff_def, SimpleGraph.edgeSet_sup,
          SimpleGraph.edgeSet_sdiff, ih, h]; omega
      · simp [faceSymmDiffList, symmDiff_def, SimpleGraph.edgeSet_sup,
          SimpleGraph.edgeSet_sdiff, ih, h]

end PottsDiscontinuity.TorusTopology.Planar.Medial
