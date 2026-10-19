/- Adapted from an earlier, unpublished formalization of the planar FK model by the same author.
Adaptation: Namespace and import relocation only. -/
module

public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.DeleteEdges
public import Mathlib.Combinatorics.SimpleGraph.Matching
public import Mathlib.Data.Finset.Max
public import Mathlib.Data.Finset.SymmDiff
public import PottsDiscontinuity.TorusTopology.PlanarParafermionicCoverFaceBoundaryGraph
public import PottsDiscontinuity.TorusTopology.PlanarParafermionicCoverFacePivotGeometry

@[expose] public section

namespace PottsDiscontinuity.TorusTopology.Planar.Medial

open PottsDiscontinuity.TorusTopology.Planar
open SimpleGraph

/-- Two retained actual faces are adjacent when their actual box-carrier
boundary graphs share an edge. -/
def parafermionicCoverFiniteFaceAdjacencyGraph (n : ℕ) :
    SimpleGraph (ParafermionicCoverFiniteFaceTopIndex n) where
  Adj i j := i ≠ j ∧ ∃ e,
    e ∈ (parafermionicCoverFiniteFaceBoundaryGraph i.1 i.2).edgeSet ∧
    e ∈ (parafermionicCoverFiniteFaceBoundaryGraph j.1 j.2).edgeSet
  symm := by
    constructor
    intro i j h
    rcases h with ⟨hne, e, hi, hj⟩
    exact ⟨hne.symm, e, hj, hi⟩
  loopless := by
    constructor
    intro i h
    exact h.1 rfl

theorem parafermionicCoverFiniteFaceAdjacencyGraph_adj_iff {n : ℕ}
    (i j : ParafermionicCoverFiniteFaceTopIndex n) :
    (parafermionicCoverFiniteFaceAdjacencyGraph n).Adj i j ↔
      i ≠ j ∧ ∃ e,
        e ∈ (parafermionicCoverFiniteFaceBoundaryGraph i.1 i.2).edgeSet ∧
        e ∈ (parafermionicCoverFiniteFaceBoundaryGraph j.1 j.2).edgeSet := Iff.rfl

/-- `none` is an adjoined boundary vertex. It is linked to an actual face
along an edge that belongs to no other retained face boundary. -/
def parafermionicCoverFiniteFaceAdjacencyWithBoundaryGraph (n : ℕ) :
    SimpleGraph (Option (ParafermionicCoverFiniteFaceTopIndex n)) where
  Adj x y := match x, y with
    | none, none => False
    | none, some j => ∃ e,
        e ∈ (parafermionicCoverFiniteFaceBoundaryGraph j.1 j.2).edgeSet ∧
        ∀ i, i ≠ j → e ∉ (parafermionicCoverFiniteFaceBoundaryGraph i.1 i.2).edgeSet
    | some i, none => ∃ e,
        e ∈ (parafermionicCoverFiniteFaceBoundaryGraph i.1 i.2).edgeSet ∧
        ∀ j, j ≠ i → e ∉ (parafermionicCoverFiniteFaceBoundaryGraph j.1 j.2).edgeSet
    | some i, some j =>
        (parafermionicCoverFiniteFaceAdjacencyGraph n).Adj i j
  symm := by
    constructor
    intro x y h
    cases x with
    | none =>
      cases y with
      | none => exact h.elim
      | some j => exact h
    | some i =>
      cases y with
      | none => exact h
      | some j =>
        rcases h with ⟨hne, e, hi, hj⟩
        exact ⟨hne.symm, e, hj, hi⟩
  loopless := by
    constructor
    intro x h
    cases x with
    | none => exact h
    | some i => exact (parafermionicCoverFiniteFaceAdjacencyGraph n).loopless.irrefl i h

theorem parafermionicCoverFiniteFaceAdjacencyWithBoundaryGraph_adj_none_some_iff
    {n : ℕ} (i : ParafermionicCoverFiniteFaceTopIndex n) :
    (parafermionicCoverFiniteFaceAdjacencyWithBoundaryGraph n).Adj none (some i) ↔
      ∃ e,
        e ∈ (parafermionicCoverFiniteFaceBoundaryGraph i.1 i.2).edgeSet ∧
        ∀ j, j ≠ i → e ∉
          (parafermionicCoverFiniteFaceBoundaryGraph j.1 j.2).edgeSet := Iff.rfl

theorem parafermionicCoverFiniteFaceAdjacencyWithBoundaryGraph_adj_some_some_iff
    {n : ℕ} (i j : ParafermionicCoverFiniteFaceTopIndex n) :
    (parafermionicCoverFiniteFaceAdjacencyWithBoundaryGraph n).Adj (some i) (some j) ↔
      i ≠ j ∧ ∃ e,
        e ∈ (parafermionicCoverFiniteFaceBoundaryGraph i.1 i.2).edgeSet ∧
        e ∈ (parafermionicCoverFiniteFaceBoundaryGraph j.1 j.2).edgeSet := Iff.rfl

end PottsDiscontinuity.TorusTopology.Planar.Medial
