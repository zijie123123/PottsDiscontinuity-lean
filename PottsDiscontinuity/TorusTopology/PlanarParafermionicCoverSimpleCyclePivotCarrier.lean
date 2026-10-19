/- Adapted from an earlier, unpublished formalization of the planar FK model by the same author.
Adaptation: Namespace and import relocation only. -/
module

public import PottsDiscontinuity.TorusTopology.PlanarParafermionicCoverFaceUnionCarrierTransport
public import PottsDiscontinuity.TorusTopology.PlanarParafermionicCoverFaceSetPivotRemoval
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.Tactic

@[expose] public section

namespace PottsDiscontinuity.TorusTopology.Planar.Medial

open PottsDiscontinuity.TorusTopology.Planar
open SimpleGraph

theorem parafermionicCoverSimpleCyclePivotGraph_induce_carrier_connected
    {n : ℕ} (hn : 1 ≤ n) {u : ParafermionicCoverBoxVertex n}
    (p : (parafermionicCoverBoxGraph n).Walk u u) (hp : p.IsCycle) :
    ((parafermionicCoverFiniteFaceSetWithoutPivotsGraph
        (parafermionicCoverSimpleCycleFillingSet hn p hp)).induce
      (parafermionicCoverFiniteFaceUnionCarrier
        (parafermionicCoverSimpleCycleFillingSet hn p hp))).Connected := by
  classical
  let S := parafermionicCoverSimpleCycleFillingSet hn p hp
  let U := parafermionicCoverFiniteFaceUnionGraph S
  let C := parafermionicCoverFiniteFaceUnionCarrier S
  let R := parafermionicCoverFiniteFaceSetWithoutPivotsGraph S
  have hRle : R ≤ U := by
    exact SimpleGraph.deleteEdges_le _
  have hreach : (R.induce C).Reachable = (U.induce C).Reachable := by
    funext x y
    apply propext
    rw [← parafermionicCoverFiniteFaceUnionCarrier_induce_reachable_iff
      S R hRle x.1 y.1 x.2 y.2,
      ← parafermionicCoverFiniteFaceUnionCarrier_induce_reachable_iff
        S U le_rfl x.1 y.1 x.2 y.2,
      parafermionicCoverFiniteFaceSetWithoutPivotsGraph_reachable_eq]
  have hUconn : (U.induce C).Connected := by
    simpa [U, C, S] using
      parafermionicCoverSimpleCycleFaceUnionCarrier_connected hn p hp
  rw [connected_iff_exists_forall_reachable] at hUconn ⊢
  rcases hUconn with ⟨a, ha⟩
  refine ⟨a, ?_⟩
  intro b
  change (R.induce C).Reachable a b
  rw [hreach]
  exact ha b

theorem parafermionicCoverFiniteFaceSetWithoutPivotsGraph_induce_carrier_edge_card_add_faces
    {n : ℕ} (S : Finset (ParafermionicCoverFiniteFaceTopIndex n)) :
    Nat.card {e // e ∈ ((parafermionicCoverFiniteFaceSetWithoutPivotsGraph S).induce
      (parafermionicCoverFiniteFaceUnionCarrier S)).edgeSet} + S.card =
      (parafermionicCoverFiniteFaceSetEdgeSupport S).card := by
  classical
  let U := parafermionicCoverFiniteFaceUnionGraph S
  let C := parafermionicCoverFiniteFaceUnionCarrier S
  let R := parafermionicCoverFiniteFaceSetWithoutPivotsGraph S
  let E := parafermionicCoverFiniteFaceSetEdgeSupport S
  let P := parafermionicCoverFiniteFaceSetPivots S
  have hRle : R ≤ U := by exact SimpleGraph.deleteEdges_le _
  have hInduce := parafermionicCoverFiniteFaceUnionCarrier_induce_edgeSet_card
    S R hRle
  have hEdge : R.edgeSet = ((E \ P : Finset _) : Set _) := by
    change ((parafermionicCoverFiniteFaceUnionGraph S).deleteEdges
      (parafermionicCoverFiniteFaceSetPivots S : Set _)).edgeSet = _
    rw [SimpleGraph.edgeSet_deleteEdges,
      parafermionicCoverFiniteFaceUnionGraph_edgeSet_eq_support]
    ext e
    simp [Set.mem_sdiff, E, P]
  have hRcard : Nat.card {e // e ∈ R.edgeSet} = (E \ P).card := by
    rw [hEdge]
    let Q : Finset (Sym2 (ParafermionicCoverBoxVertex n)) := E \ P
    have hequiv : {e : Sym2 (ParafermionicCoverBoxVertex n) // e ∈ E ∧ e ∉ P} ≃
        {e : Sym2 (ParafermionicCoverBoxVertex n) // e ∈ Q} :=
      Equiv.subtypeEquivRight (p := fun e => e ∈ E ∧ e ∉ P)
        (q := fun e => e ∈ Q) (by intro e; simp [Q, Finset.mem_sdiff])
    calc
      Nat.card {e : Sym2 (ParafermionicCoverBoxVertex n) // e ∈ Q} =
          Fintype.card {e : Sym2 (ParafermionicCoverBoxVertex n) // e ∈ E ∧ e ∉ P} := by
            rw [Nat.card_eq_fintype_card]
            exact Fintype.card_congr hequiv.symm
      _ = Q.card := by
        calc
          Fintype.card {e : Sym2 (ParafermionicCoverBoxVertex n) // e ∈ E ∧ e ∉ P} =
              Fintype.card {e : Sym2 (ParafermionicCoverBoxVertex n) // e ∈ Q} :=
                Fintype.card_congr hequiv
          _ = Q.card := by simp
  calc
    _ = Nat.card {e // e ∈ R.edgeSet} + S.card := by rw [hInduce]
    _ = (E \ P).card + S.card := by rw [hRcard]
    _ = E.card := by
      simpa [E, P] using parafermionicCoverFiniteFaceSetEdgeSupport_sdiff_pivots_card S

end PottsDiscontinuity.TorusTopology.Planar.Medial
