/- Adapted from an earlier, unpublished formalization of the planar FK model by the same author.
Adaptation: Namespace/import relocation; removed heartbeat overrides; reuse the proved union-edge-support equality. -/
module

public import Mathlib.Combinatorics.SimpleGraph.Acyclic
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Subgraph
public import Mathlib.Tactic
public import PottsDiscontinuity.TorusTopology.PlanarParafermionicCoverFaceSetBoundaryPivot
public import PottsDiscontinuity.TorusTopology.PlanarParafermionicCoverFaceSetPivotRemoval
public import PottsDiscontinuity.TorusTopology.PlanarParafermionicCoverFaceUnionCarrierTransport
public import PottsDiscontinuity.TorusTopology.PlanarParafermionicCoverSimpleCycleFillingContainment

@[expose] public section

namespace PottsDiscontinuity.TorusTopology.Planar.Medial

open PottsDiscontinuity.TorusTopology.Planar
open SimpleGraph

private theorem faceUnionGraph_edgeSet_subset_support {n : ℕ}
    (S : Finset (ParafermionicCoverFiniteFaceTopIndex n)) :
    (parafermionicCoverFiniteFaceUnionGraph S).edgeSet ⊆
      (parafermionicCoverFiniteFaceSetEdgeSupport S : Set
        (Sym2 (ParafermionicCoverBoxVertex n))) := by
  exact (parafermionicCoverFiniteFaceUnionGraph_edgeSet_eq_support S).le

/-- The graph formed by a named actual simple-cycle filling is acyclic after
deleting precisely that filling's actual top pivots. -/
theorem parafermionicCoverSimpleCyclePivotAcyclic
    {n : ℕ} (hn : 1 ≤ n) {u : ParafermionicCoverBoxVertex n}
    (p : (parafermionicCoverBoxGraph n).Walk u u) (hp : p.IsCycle) :
    (parafermionicCoverFiniteFaceSetWithoutPivotsGraph
      (parafermionicCoverSimpleCycleFillingSet hn p hp)).IsAcyclic := by
  classical
  let S := parafermionicCoverSimpleCycleFillingSet hn p hp
  let R := parafermionicCoverFiniteFaceSetWithoutPivotsGraph S
  let U := parafermionicCoverFiniteFaceUnionGraph S
  have hRleU : R ≤ U := by
    change U.deleteEdges _ ≤ U
    exact SimpleGraph.deleteEdges_le _
  have hRleBox : R ≤ parafermionicCoverBoxGraph n :=
    le_trans hRleU (parafermionicCoverFiniteFaceUnionGraph_le_boxGraph S)
  intro v q hq
  let qbox := q.mapLe hRleBox
  have hqbox : qbox.IsCycle := hq.mapLe hRleBox
  let T := parafermionicCoverSimpleCycleFillingSet hn qbox hqbox
  have hspec := parafermionicCoverSimpleCycleFillingSet_spec hn qbox hqbox
  have hTne : T.Nonempty := by simpa [T] using hspec.2.1
  have hsupport : (parafermionicCoverFiniteFaceSetBoundaryGraph T).edgeSet ⊆
      (parafermionicCoverFiniteFaceSetEdgeSupport S : Set
        (Sym2 (ParafermionicCoverBoxVertex n))) := by
    intro e he
    rw [parafermionicCoverSimpleCycleFillingSet_boundary_eq hn qbox hqbox,
      SimpleGraph.Subgraph.edgeSet_spanningCoe,
      SimpleGraph.Walk.edgeSet_toSubgraph] at he
    have heq : e ∈ q.edges := by simpa [qbox] using he
    have hRedge : e ∈ R.edgeSet := q.edges_subset_edgeSet heq
    exact faceUnionGraph_edgeSet_subset_support S (SimpleGraph.edgeSet_mono hRleU hRedge)
  have hTS : T ⊆ S := by
    exact parafermionicCoverSimpleCycleFillingSet_contains_boundary_supported_faces
      hn p hp T hsupport
  obtain ⟨i, hiT, hipivot⟩ :=
    parafermionicCoverFiniteFaceSetBoundaryGraph_exists_pivot T hTne
  have hipivotT : parafermionicCoverFiniteFaceTopPivot n i ∈
      (parafermionicCoverFiniteFaceSetBoundaryGraph T).edgeSet := hipivot
  have hiS : i ∈ S := hTS hiT
  have hipivotP : parafermionicCoverFiniteFaceTopPivot n i ∈
      (parafermionicCoverFiniteFaceSetPivots S : Set
        (Sym2 (ParafermionicCoverBoxVertex n))) := by
    change parafermionicCoverFiniteFaceTopPivot n i ∈
      parafermionicCoverFiniteFaceSetPivots S
    exact Finset.mem_image.mpr ⟨i, hiS, rfl⟩
  rw [parafermionicCoverSimpleCycleFillingSet_boundary_eq hn qbox hqbox,
    SimpleGraph.Subgraph.edgeSet_spanningCoe,
    SimpleGraph.Walk.edgeSet_toSubgraph] at hipivotT
  have hipivotR : parafermionicCoverFiniteFaceTopPivot n i ∈ R.edgeSet :=
    q.edges_subset_edgeSet (by simpa [qbox] using hipivotT)
  change parafermionicCoverFiniteFaceTopPivot n i ∈
    (U.deleteEdges
      (parafermionicCoverFiniteFaceSetPivots S : Set _)).edgeSet at hipivotR
  rw [SimpleGraph.edgeSet_deleteEdges] at hipivotR
  exact hipivotR.2 hipivotP

end PottsDiscontinuity.TorusTopology.Planar.Medial
