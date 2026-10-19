/- Adapted from an earlier, unpublished formalization of the planar FK model by the same author.
Adaptation: Namespace and import relocation only. -/
module

public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Subgraph
public import Mathlib.Tactic
public import PottsDiscontinuity.TorusTopology.PlanarParafermionicCoverFaceChainUniqueness
public import PottsDiscontinuity.TorusTopology.PlanarParafermionicCoverFaceOrientedBoundary

@[expose] public section

namespace PottsDiscontinuity.TorusTopology.Planar.Medial

open PottsDiscontinuity.TorusTopology.Planar

private theorem coverCycle_spanningCoe_even_degree {n : ℕ}
    {u : ParafermionicCoverBoxVertex n}
    (p : (parafermionicCoverBoxGraph n).Walk u u) (hp : p.IsCycle) :
    ∀ v : ParafermionicCoverBoxVertex n,
      Even ((p.toSubgraph.spanningCoe).neighborSet v).ncard := by
  classical
  let H : SimpleGraph (ParafermionicCoverBoxVertex n) := p.toSubgraph.spanningCoe
  let : DecidableRel H.Adj := Classical.decRel _
  intro v
  let q := p.transfer H (by
    intro e he
    rw [SimpleGraph.Subgraph.edgeSet_spanningCoe,
      SimpleGraph.Walk.edgeSet_toSubgraph]
    exact he)
  have hqtrail : q.IsTrail := by
    simpa [q] using hp.isTrail
  have hqedges : q.edgeSet = H.edgeSet := by
    change (p.transfer H _).edgeSet = H.edgeSet
    rw [SimpleGraph.Walk.edgeSet_transfer,
      SimpleGraph.Subgraph.edgeSet_spanningCoe,
      SimpleGraph.Walk.edgeSet_toSubgraph]
  have heuler : q.IsEulerian := hqtrail.isEulerian_iff.mpr hqedges
  have hdegree : Even (H.degree v) :=
    (heuler.even_degree_iff).2 (by intro huv; exact (huv rfl).elim)
  rw [← H.card_neighborSet_eq_degree, Set.fintypeCard_eq_ncard] at hdegree
  exact hdegree

theorem parafermionicCoverSimpleCycle_unique_face_filling {n : ℕ}
    (hn : 1 ≤ n) {u : ParafermionicCoverBoxVertex n}
    (p : (parafermionicCoverBoxGraph n).Walk u u) (hp : p.IsCycle) :
    ∃! S : Finset (ParafermionicCoverFiniteFaceTopIndex n),
      (∃ L : List (ParafermionicCoverFiniteFaceTopIndex n),
        L.Nodup ∧ L.toFinset = S ∧
          faceSymmDiffList
            (fun i => parafermionicCoverFiniteFaceBoundaryGraph i.1 i.2) L =
              p.toSubgraph.spanningCoe) ∧
      S.Nonempty ∧
      ∀ a b : ParafermionicCoverBoxVertex n,
        parafermionicCoverFaceBoundaryCoefficient S a b ≠ 0 ↔
          s(a,b) ∈ p.edges := by
  classical
  let H : SimpleGraph (ParafermionicCoverBoxVertex n) := p.toSubgraph.spanningCoe
  have hle : H ≤ parafermionicCoverBoxGraph n := by
    exact p.toSubgraph.spanningCoe_le
  have heven : ∀ v : ParafermionicCoverBoxVertex n, Even (H.neighborSet v).ncard := by
    intro v
    exact coverCycle_spanningCoe_even_degree p hp v
  obtain ⟨S, hS, hSunique⟩ :=
    parafermionicCoverFiniteFaceChain_unique_representation hn H hle heven
  obtain ⟨L, hL, hLS, hLH⟩ := hS
  have hHne : H ≠ ⊥ := by
    intro hbot
    have hadj : H.Adj u p.snd := by
      change p.toSubgraph.spanningCoe.Adj u p.snd
      exact p.toSubgraph_adj_snd hp.not_nil
    rw [hbot] at hadj
    simp at hadj
  have hLne : L ≠ [] := by
    intro hnil
    subst L
    have hbottom : faceSymmDiffList
        (fun i : ParafermionicCoverFiniteFaceTopIndex n =>
          parafermionicCoverFiniteFaceBoundaryGraph i.1 i.2)
        ([] : List (ParafermionicCoverFiniteFaceTopIndex n)) = ⊥ := by
      simp [faceSymmDiffList]
    apply hHne
    rw [← hLH, hbottom]
  have hSnonempty : S.Nonempty := by
    by_contra h
    have hsempty : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp h
    have hLnil : L = [] := by
      cases L with
      | nil => rfl
      | cons a rest =>
        have ha : a ∈ (a :: rest).toFinset := by simp
        rw [hLS, hsempty] at ha
        simp at ha
    exact hLne hLnil
  have hcoeff (a b : ParafermionicCoverBoxVertex n) :
      parafermionicCoverFaceBoundaryCoefficient S a b ≠ 0 ↔ s(a,b) ∈ p.edges := by
    have hboundary := parafermionicCoverFaceBoundaryCoefficient_ne_zero_iff
      S L hL hLS a b
    rw [hLH] at hboundary
    change parafermionicCoverFaceBoundaryCoefficient S a b ≠ 0 ↔
      s(a,b) ∈ (p.toSubgraph.spanningCoe).edgeSet at hboundary
    rw [SimpleGraph.Subgraph.edgeSet_spanningCoe,
      SimpleGraph.Walk.edgeSet_toSubgraph] at hboundary
    exact hboundary
  refine ⟨S, ⟨⟨L, hL, hLS, hLH⟩, hSnonempty, hcoeff⟩, ?_⟩
  intro T hT
  have hTrep := hT.1
  have hTunique := hSunique T hTrep
  exact hTunique

end PottsDiscontinuity.TorusTopology.Planar.Medial

namespace PottsDiscontinuity.TorusTopology.Planar.Medial

open PottsDiscontinuity.TorusTopology.Planar

noncomputable def parafermionicCoverSimpleCycleFillingSet {n : ℕ}
    (hn : 1 ≤ n) {u : ParafermionicCoverBoxVertex n}
    (p : (parafermionicCoverBoxGraph n).Walk u u) (hp : p.IsCycle) :
    Finset (ParafermionicCoverFiniteFaceTopIndex n) :=
  Classical.choose (parafermionicCoverSimpleCycle_unique_face_filling hn p hp).exists

theorem parafermionicCoverSimpleCycleFillingSet_spec {n : ℕ}
    (hn : 1 ≤ n) {u : ParafermionicCoverBoxVertex n}
    (p : (parafermionicCoverBoxGraph n).Walk u u) (hp : p.IsCycle) :
    (∃ L : List (ParafermionicCoverFiniteFaceTopIndex n),
      L.Nodup ∧ L.toFinset = parafermionicCoverSimpleCycleFillingSet hn p hp ∧
        faceSymmDiffList
          (fun i => parafermionicCoverFiniteFaceBoundaryGraph i.1 i.2) L =
            p.toSubgraph.spanningCoe) ∧
    (parafermionicCoverSimpleCycleFillingSet hn p hp).Nonempty ∧
    ∀ a b : ParafermionicCoverBoxVertex n,
      parafermionicCoverFaceBoundaryCoefficient
          (parafermionicCoverSimpleCycleFillingSet hn p hp) a b ≠ 0 ↔
        s(a,b) ∈ p.edges := by
  exact Classical.choose_spec
    (parafermionicCoverSimpleCycle_unique_face_filling hn p hp).exists

end PottsDiscontinuity.TorusTopology.Planar.Medial
