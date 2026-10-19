/- Adapted from an earlier, unpublished formalization of the planar FK model by the same author.
Adaptation: Namespace and import relocation only. -/
module

public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Acyclic
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Subgraph
public import Mathlib.Combinatorics.SimpleGraph.DeleteEdges
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Combinatorics.SimpleGraph.Matching
public import Mathlib.Combinatorics.SimpleGraph.Paths
public import Mathlib.Combinatorics.SimpleGraph.Trails
public import Mathlib.Combinatorics.SimpleGraph.Walk.Basic
public import Mathlib.Combinatorics.SimpleGraph.Walk.Maps
public import Mathlib.Data.Finset.Max
public import Mathlib.Data.Finset.SymmDiff
public import PottsDiscontinuity.TorusTopology.PlanarParafermionicCoverFiniteFaces

@[expose] public section

namespace PottsDiscontinuity.TorusTopology.Planar.Medial

open PottsDiscontinuity.TorusTopology.Planar

theorem parafermionicCoverFaceBaseCorner_injective :
    Function.Injective (fun f : ParafermionicCoverVertex => f) := by
  intro f g h
  exact h

theorem parafermionicCoverFaceRightCorner_injective :
    Function.Injective (fun f : ParafermionicCoverVertex =>
      parafermionicCoverFaceRightLift f.1.1 f.1.2 f.2) := by
  intro f g h
  rcases f with ⟨⟨x,y⟩,k⟩
  rcases g with ⟨⟨x',y'⟩,k'⟩
  simp only [parafermionicCoverFaceRightLift_formula, Prod.mk.injEq] at h
  rcases h with ⟨⟨hx,hy⟩,hk⟩
  simp only [Prod.mk.injEq]
  exact ⟨⟨by omega, by omega⟩, by omega⟩

theorem parafermionicCoverFaceRightUpCorner_injective :
    Function.Injective (fun f : ParafermionicCoverVertex =>
      parafermionicCoverFaceRightUpLift f.1.1 f.1.2 f.2) := by
  intro f g h
  rcases f with ⟨⟨x,y⟩,k⟩
  rcases g with ⟨⟨x',y'⟩,k'⟩
  simp only [parafermionicCoverFaceRightUpLift_formula, Prod.mk.injEq] at h
  rcases h with ⟨⟨hx,hy⟩,hk⟩
  simp only [Prod.mk.injEq]
  exact ⟨⟨by omega, by omega⟩, by omega⟩

theorem parafermionicCoverFaceRightUpLeftCorner_injective :
    Function.Injective (fun f : ParafermionicCoverVertex =>
      parafermionicCoverFaceRightUpLeftLift f.1.1 f.1.2 f.2) := by
  intro f g h
  rcases f with ⟨⟨x,y⟩,k⟩
  rcases g with ⟨⟨x',y'⟩,k'⟩
  simp only [parafermionicCoverFaceRightUpLeftLift_formula, Prod.mk.injEq] at h
  rcases h with ⟨⟨hx,hy⟩,hk⟩
  simp only [Prod.mk.injEq]
  exact ⟨⟨by omega, by omega⟩, by omega⟩

end PottsDiscontinuity.TorusTopology.Planar.Medial
