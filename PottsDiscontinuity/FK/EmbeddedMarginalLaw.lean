/- Adapted from an earlier, unpublished formalization of the planar FK model by the same author.
Parameter generalization: independent 0 < p < 1 and 1 ≤ q, with no upper bound on q. -/
module

public import PottsDiscontinuity.FK.IsolatedBoundaryLaw
public import PottsDiscontinuity.FK.SubgraphComparison

@[expose] public section

namespace PottsDiscontinuity.FK

noncomputable section

variable {V W : Type*} [Finite V] [Finite W]
  (G : SimpleGraph V) (H : SimpleGraph W) (f : V ↪ W)
  (hGH : G.map f ≤ H)

local instance embeddedMarginalOuterEdgeFintype : Fintype H.edgeSet := Fintype.ofFinite _
local instance embeddedMarginalOuterEdgeDecidableEq : DecidableEq H.edgeSet := Classical.decEq _
local instance embeddedMarginalInnerEdgeFintype : Fintype G.edgeSet := Fintype.ofFinite _
local instance embeddedMarginalInnerMappedEdgeFintype : Fintype (G.map f).edgeSet := Fintype.ofFinite _
local instance embeddedMarginalRemainingFintype
    (R : Configuration H) : Fintype (RemainingConfiguration H R) := Fintype.ofFinite _
local instance embeddedMarginalRemovedFintype
    (R : Configuration H) : Fintype (RemovedConfiguration H R) := Fintype.ofFinite _

omit [Finite V] in
private theorem embeddedConfigurationRestriction_union_subgraphRemoved
    (K : RemovedConfiguration H (subgraphRemovedEdges (G.map f) H))
    (A : Configuration H) :
    embeddedConfigurationRestriction G H f hGH (A ∪ K.val) =
      embeddedConfigurationRestriction G H f hGH A := by
  classical
  have hmapped (e : G.edgeSet) :
      (embeddedEdgeEmbedding G H f hGH e).val ∈ (G.map f).edgeSet := by
    rw [embeddedEdgeEmbedding_coe]
    exact (isolatedExtensionEdgeEquiv G f e).property
  have hnot (e : G.edgeSet) : embeddedEdgeEmbedding G H f hGH e ∉ K.val := by
    intro heK
    have heR : embeddedEdgeEmbedding G H f hGH e ∈ subgraphRemovedEdges (G.map f) H :=
      K.property heK
    exact ((mem_subgraphRemovedEdges (embeddedEdgeEmbedding G H f hGH e)).mp heR)
      (hmapped e)
  apply Finset.ext
  intro e
  rw [mem_embeddedConfigurationRestriction, mem_embeddedConfigurationRestriction,
    Finset.mem_union]
  constructor
  · rintro (heA | heK)
    · exact heA
    · exact (hnot e heK).elim
  · intro heA
    exact Or.inl heA

private theorem remainingLaw_map_embeddedRestriction
    (q : Parameters) (B : BoundaryCondition W)
    (K : RemovedConfiguration H (subgraphRemovedEdges (G.map f) H)) :
    (remainingLaw H q (frozenBoundary B K.val)
      (subgraphRemovedEdges (G.map f) H)).map
        (fun C => embeddedConfigurationRestriction G H f hGH
          (C.val ∪ K.val)) =
      law G q (isolatedExtensionPullbackBoundary f (frozenBoundary B K.val)) := by
  let R : Configuration H := subgraphRemovedEdges (G.map f) H
  let E : Configuration (G.map f) ≃ RemainingConfiguration H R :=
    subgraphRemainingConfigurationEquiv hGH
  let I : Configuration G ≃ Configuration (G.map f) := isolatedExtensionConfigurationEquiv G f
  have hsub : (law (G.map f) q (frozenBoundary B K.val)).map E =
      remainingLaw H q (frozenBoundary B K.val) R := by
    exact law_subgraphRemaining_map hGH q (frozenBoundary B K.val)
  have hrem :
      (remainingLaw H q (frozenBoundary B K.val) R).map E.symm =
        law (G.map f) q (frozenBoundary B K.val) := by
    calc
      _ = ((law (G.map f) q (frozenBoundary B K.val)).map E).map E.symm := by rw [hsub]
      _ = law (G.map f) q (frozenBoundary B K.val) := by
        rw [PMF.map_comp]
        have hcomp : E.symm ∘ E = id := by
          funext C
          exact E.symm_apply_apply C
        rw [hcomp, PMF.map_id]
  have hiso : (law G q (isolatedExtensionPullbackBoundary f
      (frozenBoundary B K.val))).map I =
        law (G.map f) q (frozenBoundary B K.val) := by
    exact law_isolatedExtension_map_boundary_pullback G f q (frozenBoundary B K.val)
  have hback : (law (G.map f) q (frozenBoundary B K.val)).map I.symm =
      law G q (isolatedExtensionPullbackBoundary f (frozenBoundary B K.val)) := by
    calc
      _ = ((law G q (isolatedExtensionPullbackBoundary f
          (frozenBoundary B K.val))).map I).map I.symm := by rw [hiso]
      _ = law G q (isolatedExtensionPullbackBoundary f
          (frozenBoundary B K.val)) := by
        rw [PMF.map_comp]
        have hcomp : I.symm ∘ I = id := by
          funext C
          exact I.symm_apply_apply C
        rw [hcomp, PMF.map_id]
  have hfun : (fun C : RemainingConfiguration H R => I.symm (E.symm C)) =
      (fun C => embeddedConfigurationRestriction G H f hGH (C.val ∪ K.val)) := by
    funext C
    change (isolatedExtensionConfigurationEquiv G f).symm
        (subgraphConfigurationRestriction hGH C.val) =
      embeddedConfigurationRestriction G H f hGH (C.val ∪ K.val)
    rw [embeddedConfigurationRestriction_union_subgraphRemoved G H f hGH K C.val]
    rfl
  calc
    (remainingLaw H q (frozenBoundary B K.val) R).map
        (fun C => embeddedConfigurationRestriction G H f hGH (C.val ∪ K.val)) =
      (remainingLaw H q (frozenBoundary B K.val) R).map
        (fun C => I.symm (E.symm C)) := by rw [hfun]
    _ = ((remainingLaw H q (frozenBoundary B K.val) R).map E.symm).map I.symm := by
      calc
        _ = (remainingLaw H q (frozenBoundary B K.val) R).map
            (I.symm ∘ E.symm) := by
              congr 1
        _ = _ := by rw [PMF.map_comp]
    _ = law G q (isolatedExtensionPullbackBoundary f (frozenBoundary B K.val)) := by
      rw [hrem, hback]

/-- The true outer FK law, restricted to the embedded graph, is the mixture of
the exact inner FK laws induced by each actual removed-edge state. -/
theorem law_embeddedConfigurationRestriction_eq_bind_frozenMarginal
    (q : Parameters) (ξ : BoundaryCondition W) :
    (law H q ξ).map (embeddedConfigurationRestriction G H f hGH) =
      (frozenMarginalLaw q ξ (subgraphRemovedEdges (G.map f) H)).bind
        (fun K => law G q (isolatedExtensionPullbackBoundary f
          (frozenBoundary ξ K.val))) := by
  let R : Configuration H := subgraphRemovedEdges (G.map f) H
  let split : Configuration H → RemainingConfiguration H R :=
    fun C => (configurationSplitEquiv H R C).1
  let S : RemainingConfiguration H R → Configuration G :=
    fun C => (isolatedExtensionConfigurationEquiv G f).symm
      ((subgraphRemainingConfigurationEquiv hGH).symm C)
  have hcompose : (fun C : Configuration H => S (split C)) =
      embeddedConfigurationRestriction G H f hGH := by
    funext C
    dsimp [S, split, R]
    rw [subgraphRemainingConfigurationEquiv_symm_split]
    rfl
  calc
    (law H q ξ).map (embeddedConfigurationRestriction G H f hGH) =
        (law H q ξ).map (S ∘ split) := by
          exact (congrArg (fun k => (law H q ξ).map k) hcompose).symm
    _ = ((law H q ξ).map split).map S := by
      rw [PMF.map_comp]
    _ = (frozenMarginalLaw q ξ R).bind
        (fun K => (remainingLaw H q (frozenBoundary ξ K.val) R).map S) := by
      rw [law_map_remaining_eq_bind_frozen, PMF.map_bind]
    _ = (frozenMarginalLaw q ξ R).bind
        (fun K => law G q (isolatedExtensionPullbackBoundary f
          (frozenBoundary ξ K.val))) := by
      apply congrArg (PMF.bind (frozenMarginalLaw q ξ R))
      funext K
      have hS : S = (fun C : RemainingConfiguration H R =>
          embeddedConfigurationRestriction G H f hGH (C.val ∪ K.val)) := by
        funext C
        change embeddedConfigurationRestriction G H f hGH C.val =
          embeddedConfigurationRestriction G H f hGH (C.val ∪ K.val)
        exact (embeddedConfigurationRestriction_union_subgraphRemoved
          G H f hGH K C.val).symm
      rw [hS]
      exact remainingLaw_map_embeddedRestriction G H f hGH q ξ K

end
end PottsDiscontinuity.FK
