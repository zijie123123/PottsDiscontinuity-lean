/- Adapted from an earlier, unpublished formalization of the planar FK model by the same author.
Adaptation: Namespace and import relocation only. -/
module

public import PottsDiscontinuity.TorusTopology.PlanarParafermionicCoverSimpleCyclePivotAcyclic
public import PottsDiscontinuity.TorusTopology.PlanarParafermionicCoverSimpleCyclePivotCarrier
public import Mathlib.Combinatorics.SimpleGraph.Acyclic
public import Mathlib.Tactic

@[expose] public section

namespace PottsDiscontinuity.TorusTopology.Planar.Medial

open PottsDiscontinuity.TorusTopology.Planar
open SimpleGraph

/-- The actual pivot-deleted graph of a named actual simple-cycle filling is a
 tree when induced on the original carrier of its actual face union. -/
theorem parafermionicCoverSimpleCycleFilling_inducedGraph_isTree
    {n : ℕ} (hn : 1 ≤ n) {u : ParafermionicCoverBoxVertex n}
    (p : (parafermionicCoverBoxGraph n).Walk u u) (hp : p.IsCycle) :
    ((parafermionicCoverFiniteFaceSetWithoutPivotsGraph
        (parafermionicCoverSimpleCycleFillingSet hn p hp)).induce
      (parafermionicCoverFiniteFaceUnionCarrier
        (parafermionicCoverSimpleCycleFillingSet hn p hp))).IsTree := by
  let S := parafermionicCoverSimpleCycleFillingSet hn p hp
  let R := parafermionicCoverFiniteFaceSetWithoutPivotsGraph S
  let C := parafermionicCoverFiniteFaceUnionCarrier S
  have hconnected : (R.induce C).Connected := by
    simpa [R, C, S] using
      parafermionicCoverSimpleCyclePivotGraph_induce_carrier_connected hn p hp
  have hacyclic : R.IsAcyclic := by
    simpa [R, S] using parafermionicCoverSimpleCyclePivotAcyclic hn p hp
  exact ⟨hconnected, hacyclic.induce C⟩

/-- Euler's vertex-edge count for the actual tree obtained from a named
simple-cycle filling and its actual retained-face union carrier. -/
theorem parafermionicCoverSimpleCycleFilling_euler_count
    {n : ℕ} (hn : 1 ≤ n) {u : ParafermionicCoverBoxVertex n}
    (p : (parafermionicCoverBoxGraph n).Walk u u) (hp : p.IsCycle) :
    Nat.card (parafermionicCoverFiniteFaceUnionCarrier
      (parafermionicCoverSimpleCycleFillingSet hn p hp)) +
      (parafermionicCoverSimpleCycleFillingSet hn p hp).card =
      (parafermionicCoverFiniteFaceSetEdgeSupport
        (parafermionicCoverSimpleCycleFillingSet hn p hp)).card + 1 := by
  classical
  let S := parafermionicCoverSimpleCycleFillingSet hn p hp
  let R := parafermionicCoverFiniteFaceSetWithoutPivotsGraph S
  let C := parafermionicCoverFiniteFaceUnionCarrier S
  let H := R.induce C
  have htree : H.IsTree := by
    simpa [H, R, C, S] using
      parafermionicCoverSimpleCycleFilling_inducedGraph_isTree hn p hp
  have htreeCard := htree.card_edgeFinset
  have hnat : Nat.card {e // e ∈ H.edgeSet} + 1 = Nat.card C := by
    calc
      Nat.card {e // e ∈ H.edgeSet} + 1 =
          Fintype.card {e // e ∈ H.edgeSet} + 1 := by
            rw [Nat.card_eq_fintype_card]
      _ = Finset.card H.edgeFinset + 1 := by
        rw [← SimpleGraph.edgeFinset_card]
      _ = Fintype.card C := by simpa [H] using htreeCard
      _ = Nat.card C := by rw [Nat.card_eq_fintype_card]
  have hcount :=
    parafermionicCoverFiniteFaceSetWithoutPivotsGraph_induce_carrier_edge_card_add_faces S
  have hcount' : Nat.card {e // e ∈ H.edgeSet} + S.card =
      (parafermionicCoverFiniteFaceSetEdgeSupport S).card := by
    simpa [H, R, C] using hcount
  change Nat.card C + S.card =
    (parafermionicCoverFiniteFaceSetEdgeSupport S).card + 1
  omega

end PottsDiscontinuity.TorusTopology.Planar.Medial
