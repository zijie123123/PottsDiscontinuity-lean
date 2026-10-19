/- Adapted from an earlier, unpublished formalization of the planar FK model by the same author.
Parameter generalization: independent 0 < p < 1 and 1 ≤ q, with no upper bound on q. -/
module

public import PottsDiscontinuity.FK.ConditionalLaw
public import PottsDiscontinuity.FK.IsolatedBoundaryLaw
public import PottsDiscontinuity.FK.SubgraphComparison

@[expose] public section

namespace PottsDiscontinuity.FK

noncomputable section

variable {V W : Type*} [Finite V] [Finite W]
  (G : SimpleGraph V) (H : SimpleGraph W) (f : V ↪ W)
  (hGH : G.map f ≤ H)

local instance conditionalEmbeddedLawSmallEdgeFintype : Fintype G.edgeSet := Fintype.ofFinite _
local instance conditionalEmbeddedLawMappedEdgeFintype : Fintype (G.map f).edgeSet := Fintype.ofFinite _
local instance conditionalEmbeddedLawLargeEdgeFintype : Fintype H.edgeSet := Fintype.ofFinite _
local instance conditionalEmbeddedLawLargeEdgeDecidableEq : DecidableEq H.edgeSet := Classical.decEq _
local instance conditionalEmbeddedLawRemainingFintype
    (R : Configuration H) : Fintype (RemainingConfiguration H R) := Fintype.ofFinite _
local instance conditionalEmbeddedLawRemovedFintype
    (R : Configuration H) : Fintype (RemovedConfiguration H R) := Fintype.ofFinite _

/-- Conditioning on an exact state of all non-inner edges and restricting to
an embedded inner graph gives its FK law with every exterior induced
connection retained in the pulled-back boundary partition. -/
theorem law_filter_frozen_map_embeddedRestriction
    (q : Parameters) (ξ : BoundaryCondition W)
    (K : RemovedConfiguration H (subgraphRemovedEdges (G.map f) H)) :
    ((law H q ξ).filter
      (frozenStateEvent (subgraphRemovedEdges (G.map f) H) K)
      (frozenStateEvent_support q ξ (subgraphRemovedEdges (G.map f) H) K)).map
        (embeddedConfigurationRestriction G H f hGH) =
      law G q
        (isolatedExtensionPullbackBoundary f (frozenBoundary ξ K.val)) := by
  let R : Configuration H := subgraphRemovedEdges (G.map f) H
  let B : BoundaryCondition W := frozenBoundary ξ K.val
  let E : Configuration (G.map f) ≃ RemainingConfiguration H R :=
    subgraphRemainingConfigurationEquiv hGH
  let split : Configuration H → RemainingConfiguration H R :=
    fun C => (configurationSplitEquiv H R C).1
  let Q : PMF (Configuration H) :=
    (law H q ξ).filter (frozenStateEvent R K) (frozenStateEvent_support q ξ R K)
  have hfrozen := law_filter_frozen_map_remaining q ξ R K
  have hsub := law_subgraphRemaining_map hGH q B
  have hconditional : Q.map split =
      (law (G.map f) q B).map E := by
    simpa [Q, split, R, B, E] using hfrozen.trans hsub.symm
  have hremove : (Q.map (fun C => E.symm (split C))) = law (G.map f) q B := by
    calc
      PMF.map (fun C => E.symm (split C)) Q = PMF.map (E.symm ∘ split) Q := by
        congr 1
      _ = PMF.map E.symm (PMF.map split Q) := by rw [PMF.map_comp]
      _ = PMF.map E.symm (PMF.map E (law (G.map f) q B)) :=
        congrArg (PMF.map E.symm) hconditional
      _ = law (G.map f) q B := by
        rw [PMF.map_comp]
        simp only [Function.comp_def, Equiv.symm_apply_apply]
        exact PMF.map_id (law (G.map f) q B)
  have hback : PMF.map (isolatedExtensionConfigurationEquiv G f).symm
      (law (G.map f) q B) = law G q (isolatedExtensionPullbackBoundary f B) := by
    have h := congrArg
      (fun μ : PMF (Configuration (G.map f)) =>
        PMF.map (isolatedExtensionConfigurationEquiv G f).symm μ)
      (law_isolatedExtension_map_boundary_pullback G f q B)
    simpa [PMF.map_comp, PMF.map_id] using h.symm
  have hinner : (Q.map (fun C =>
      (isolatedExtensionConfigurationEquiv G f).symm (E.symm (split C)))) =
      law G q (isolatedExtensionPullbackBoundary f B) := by
    calc
      PMF.map (fun C => (isolatedExtensionConfigurationEquiv G f).symm
          (E.symm (split C))) Q =
        PMF.map ((isolatedExtensionConfigurationEquiv G f).symm ∘
          (fun C => E.symm (split C))) Q := by
        congr 1
      _ = PMF.map (isolatedExtensionConfigurationEquiv G f).symm
          (PMF.map (fun C => E.symm (split C)) Q) := by rw [PMF.map_comp]
      _ = PMF.map (isolatedExtensionConfigurationEquiv G f).symm
          (law (G.map f) q B) := congrArg _ hremove
      _ = law G q (isolatedExtensionPullbackBoundary f B) := hback
  have hfun : (fun C =>
      (isolatedExtensionConfigurationEquiv G f).symm (E.symm (split C))) =
      embeddedConfigurationRestriction G H f hGH := by
    funext C
    dsimp [E, split, R]
    rw [subgraphRemainingConfigurationEquiv_symm_split]
    rfl
  rw [← hfun]
  simpa [Q, B] using hinner

end
end PottsDiscontinuity.FK
