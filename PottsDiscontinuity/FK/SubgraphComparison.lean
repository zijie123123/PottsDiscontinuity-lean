/- Adapted from an earlier, unpublished formalization of the planar FK model by the same author.
Parameter generalization: independent 0 < p < 1 and 1 ≤ q, with no upper bound on q. -/
module

public import PottsDiscontinuity.FK.IsolatedExtension
public import PottsDiscontinuity.FK.VolumeComparison
public import Mathlib.Data.Finset.Preimage

/-!
# Free FK comparison under actual finite graph inclusions

Configurations are transported along injective maps of original unordered edges.
Restriction retains exactly the sampled states of the smaller graph. The proof
uses the complete conditional FK mixture, and counts added isolated vertices
before cancelling their common weight factor.
-/

@[expose] public section

namespace PottsDiscontinuity.FK

open FiniteProbability
noncomputable section

section SameVertices

variable {V : Type*} {G H : SimpleGraph V} (hGH : G ≤ H)

/-- Inclusion of the original unordered edges of a same-vertex subgraph. -/
def subgraphEdgeEmbedding : G.edgeSet ↪ H.edgeSet where
  toFun e := ⟨e.val, SimpleGraph.edgeSet_mono hGH e.property⟩
  inj' := by
    intro a b h
    exact Subtype.ext (congrArg (fun e : H.edgeSet => e.val) h)

@[simp] theorem subgraphEdgeEmbedding_coe (e : G.edgeSet) :
    (subgraphEdgeEmbedding hGH e).val = e.val := rfl

/-- Embed a configuration by leaving every additional edge closed. -/
def subgraphConfigurationEmbedding : Configuration G ↪ Configuration H where
  toFun A := A.map (subgraphEdgeEmbedding hGH)
  inj' := Finset.map_injective _

/-- Restrict a full configuration to exactly the original subgraph edges. -/
def subgraphConfigurationRestriction (A : Configuration H) : Configuration G :=
  A.preimage (subgraphEdgeEmbedding hGH) (subgraphEdgeEmbedding hGH).injective.injOn

@[simp] theorem mem_subgraphConfigurationRestriction (A : Configuration H) (e : G.edgeSet) :
    e ∈ subgraphConfigurationRestriction hGH A ↔ subgraphEdgeEmbedding hGH e ∈ A :=
  Finset.mem_preimage

@[simp] theorem subgraphConfigurationRestriction_embedding (A : Configuration G) :
    subgraphConfigurationRestriction hGH (subgraphConfigurationEmbedding hGH A) = A :=
  Finset.preimage_map _ _

theorem subgraphConfigurationRestriction_monotone : Monotone (subgraphConfigurationRestriction hGH) :=
  Finset.monotone_preimage (subgraphEdgeEmbedding hGH).injective

/-- The open graph keeps the same vertices and exactly the same selected edges. -/
theorem openGraph_subgraphConfigurationEmbedding (A : Configuration G) :
    openGraph H (subgraphConfigurationEmbedding hGH A) = openGraph G A := by
  unfold openGraph openEdges
  change SimpleGraph.fromEdgeSet (Subtype.val '' (↑(A.map (subgraphEdgeEmbedding hGH)) : Set H.edgeSet)) = _
  simp only [Finset.coe_map, Set.image_image]
  rfl

variable [Finite V]
local instance subgraphComparisonSmallEdgeFintype : Fintype G.edgeSet := Fintype.ofFinite _
local instance subgraphComparisonLargeEdgeFintype : Fintype H.edgeSet := Fintype.ofFinite _
local instance subgraphComparisonLargeEdgeDecidableEq : DecidableEq H.edgeSet := Classical.decEq _

/-- All large-graph edges absent from the actual subgraph. -/
def subgraphRemovedEdges (G H : SimpleGraph V) : Configuration H := by
  classical
  exact Finset.univ.filter (fun e => e.val ∉ G.edgeSet)

@[simp] theorem mem_subgraphRemovedEdges (e : H.edgeSet) :
    e ∈ subgraphRemovedEdges G H ↔ e.val ∉ G.edgeSet := by
  classical
  simp [subgraphRemovedEdges]

include hGH in
/-- Deleting that full complement recovers the actual subgraph on the same vertices. -/
theorem edgeRestriction_subgraphRemovedEdges :
    edgeRestriction H (subgraphRemovedEdges G H) = G := by
  apply SimpleGraph.edgeSet_injective
  rw [edgeRestriction_edgeSet]
  ext e
  constructor
  · rintro ⟨heH, heR⟩
    by_contra heG
    exact heR ⟨⟨e, heH⟩, (mem_subgraphRemovedEdges _).mpr heG, rfl⟩
  · intro heG
    refine ⟨SimpleGraph.edgeSet_mono hGH heG, ?_⟩
    rintro ⟨e, heR, rfl⟩
    exact (mem_subgraphRemovedEdges e).mp heR heG

/-- Configurations of a subgraph are all and only the remaining-edge configurations. -/
def subgraphRemainingConfigurationEquiv :
    Configuration G ≃ RemainingConfiguration H (subgraphRemovedEdges G H) where
  toFun A := ⟨subgraphConfigurationEmbedding hGH A, by
    classical
    apply Finset.disjoint_left.mpr
    intro e he heR
    obtain ⟨a, ha, rfl⟩ := Finset.mem_map.mp he
    exact (mem_subgraphRemovedEdges _).mp heR a.property⟩
  invFun A := subgraphConfigurationRestriction hGH A.val
  left_inv := subgraphConfigurationRestriction_embedding hGH
  right_inv A := by
    classical
    apply Subtype.ext
    apply Finset.ext
    intro e
    constructor
    · intro he
      obtain ⟨a, ha, rfl⟩ := Finset.mem_map.mp he
      exact (mem_subgraphConfigurationRestriction hGH A.val a).mp ha
    · intro he
      have heG : e.val ∈ G.edgeSet := by
        by_contra hn
        exact Finset.disjoint_left.mp A.property he ((mem_subgraphRemovedEdges e).mpr hn)
      exact Finset.mem_map.mpr ⟨⟨e.val, heG⟩, Finset.mem_preimage.mpr he, rfl⟩

@[simp] theorem subgraphRemainingConfigurationEquiv_val (A : Configuration G) :
    (subgraphRemainingConfigurationEquiv hGH A).val = subgraphConfigurationEmbedding hGH A := rfl

/-- The actual open-edge inclusion order is preserved in both directions. -/
def subgraphRemainingConfigurationOrderIso :
    Configuration G ≃o RemainingConfiguration H (subgraphRemovedEdges G H) where
  toEquiv := subgraphRemainingConfigurationEquiv hGH
  map_rel_iff' := Finset.map_subset_map

/-- Restricting before or after discarding the complement keeps the same edge states. -/
theorem subgraphRemainingConfigurationEquiv_symm_split (A : Configuration H) :
    (subgraphRemainingConfigurationEquiv hGH).symm
        (configurationSplitEquiv H (subgraphRemovedEdges G H) A).1 =
      subgraphConfigurationRestriction hGH A := by
  classical
  apply Finset.ext
  intro e
  change e ∈ subgraphConfigurationRestriction hGH (A \ subgraphRemovedEdges G H) ↔ _
  rw [mem_subgraphConfigurationRestriction]
  simp only [Finset.mem_sdiff, mem_subgraphRemovedEdges, subgraphEdgeEmbedding_coe,
    e.property, not_true_eq_false, not_false_eq_true, and_true,
    mem_subgraphConfigurationRestriction]

include hGH in
/-- Counts of sampled edges agree exactly, including the closed-edge exponent. -/
theorem subgraph_edge_card : Nat.card H.edgeSet - (subgraphRemovedEdges G H).card =
    Nat.card G.edgeSet := by
  rw [← edgeRestriction_card, edgeRestriction_subgraphRemovedEdges hGH]

/-- The reduced weight is the ordinary FK weight on the genuine subgraph. -/
theorem remainingWeight_subgraph (q : Parameters) (ξ : BoundaryCondition V)
    (A : Configuration G) :
    remainingWeight H q ξ (subgraphRemovedEdges G H) (subgraphRemainingConfigurationEquiv hGH A) =
      weight G q ξ A := by
  have hc : componentCount H ξ (subgraphConfigurationEmbedding hGH A) = componentCount G ξ A := by
    simp only [componentCount, componentSetoid, openGraph_subgraphConfigurationEmbedding]
  rw [remainingWeight, subgraphRemainingConfigurationEquiv_val, weight, subgraph_edge_card hGH, hc]
  change _ ^ (A.map _).card * _ ^ (_ - (A.map _).card) * _ = _
  rw [Finset.card_map]

local instance subgraphComparisonRemainingFintype :
    Fintype (RemainingConfiguration H (subgraphRemovedEdges G H)) := Fintype.ofFinite _

/-- Exact whole-law transport from the actual subgraph to the remaining-edge model. -/
theorem law_subgraphRemaining_map (q : Parameters) (ξ : BoundaryCondition V) :
    (law G q ξ).map (subgraphRemainingConfigurationEquiv hGH) =
      remainingLaw H q ξ (subgraphRemovedEdges G H) := by
  unfold law remainingLaw
  apply pmf_map_equiv_of_weight_eq
  intro A
  exact (remainingWeight_subgraph hGH q ξ A).symm

/-- Adding graph edges increases every nonnegative increasing observable of the
original edges, with the same actual vertex carrier and boundary partition. -/
theorem subgraph_expectation_le (q : Parameters) (ξ : BoundaryCondition V)
    (F : Configuration G → ℝ) (hF0 : ∀ A, 0 ≤ F A) (hF : Monotone F) :
    expectation (law G q ξ) F ≤
      expectation (law H q ξ) (fun A => F (subgraphConfigurationRestriction hGH A)) := by
  have h := remainingLaw_le_original_expectation q ξ (subgraphRemovedEdges G H)
    (fun A => F ((subgraphRemainingConfigurationEquiv hGH).symm A))
    (fun A => hF0 _) (hF.comp (subgraphRemainingConfigurationOrderIso hGH).symm.monotone)
  rw [← law_subgraphRemaining_map hGH, expectation_map] at h
  simpa only [Equiv.symm_apply_apply, subgraphRemainingConfigurationEquiv_symm_split] using h

end SameVertices

section EmbeddedVertices

variable {V W : Type*} (G : SimpleGraph V) (H : SimpleGraph W)
  (f : V ↪ W) (hGH : G.map f ≤ H)

/-- The original unordered edge, with its endpoints mapped into the larger graph. -/
def embeddedEdgeEmbedding : G.edgeSet ↪ H.edgeSet :=
  (isolatedExtensionEdgeEquiv G f).toEmbedding.trans (subgraphEdgeEmbedding hGH)

@[simp] theorem embeddedEdgeEmbedding_coe (e : G.edgeSet) :
    (embeddedEdgeEmbedding G H f hGH e).val = f.sym2Map e.val := rfl

/-- Leave every edge outside the embedded original graph closed. -/
def embeddedConfigurationEmbedding : Configuration G ↪ Configuration H :=
  (isolatedExtensionConfigurationEquiv G f).toEmbedding.trans (subgraphConfigurationEmbedding hGH)

/-- Read exactly the states of the original embedded edges of the larger configuration. -/
def embeddedConfigurationRestriction (A : Configuration H) : Configuration G :=
  (isolatedExtensionConfigurationEquiv G f).symm (subgraphConfigurationRestriction hGH A)

/-- The configuration embedding is the literal finite image along original edges. -/
theorem embeddedConfigurationEmbedding_eq_map (A : Configuration G) :
    embeddedConfigurationEmbedding G H f hGH A = A.map (embeddedEdgeEmbedding G H f hGH) := by
  change (A.map (isolatedExtensionEdgeEquiv G f).toEmbedding).map (subgraphEdgeEmbedding hGH) = _
  exact Finset.map_map _ _ _

/-- Restriction reads exactly the large-graph state of each embedded original edge. -/
@[simp] theorem mem_embeddedConfigurationRestriction (A : Configuration H) (e : G.edgeSet) :
    e ∈ embeddedConfigurationRestriction G H f hGH A ↔ embeddedEdgeEmbedding G H f hGH e ∈ A := by
  simp only [embeddedConfigurationRestriction, isolatedExtensionConfigurationEquiv,
    Equiv.finsetCongr_symm, Equiv.finsetCongr_apply, Finset.mem_map_equiv,
    Equiv.symm_symm, mem_subgraphConfigurationRestriction]
  rfl

@[simp] theorem embeddedConfigurationRestriction_embedding (A : Configuration G) :
    embeddedConfigurationRestriction G H f hGH (embeddedConfigurationEmbedding G H f hGH A) = A := by
  change (isolatedExtensionConfigurationEquiv G f).symm
    (subgraphConfigurationRestriction hGH
      (subgraphConfigurationEmbedding hGH (isolatedExtensionConfigurationEquiv G f A))) = A
  rw [subgraphConfigurationRestriction_embedding, Equiv.symm_apply_apply]

/-- Reading original edges and extending by closed edges is contained in the
actual full configuration, including when the two vertex carriers differ. -/
theorem embeddedConfigurationEmbedding_restriction_subset (A : Configuration H) :
    embeddedConfigurationEmbedding G H f hGH (embeddedConfigurationRestriction G H f hGH A) ⊆ A := by
  rw [embeddedConfigurationEmbedding_eq_map]
  intro e he
  obtain ⟨a, ha, rfl⟩ := Finset.mem_map.mp he
  exact (mem_embeddedConfigurationRestriction G H f hGH A a).mp ha

theorem embeddedConfigurationRestriction_monotone : Monotone (embeddedConfigurationRestriction G H f hGH) :=
  (isolatedExtensionConfigurationOrderIso G f).symm.monotone.comp
    (subgraphConfigurationRestriction_monotone hGH)

variable [Finite V] [Finite W]
local instance subgraphComparisonEmbeddedSmallEdgeFintype : Fintype G.edgeSet := Fintype.ofFinite _
local instance subgraphComparisonEmbeddedMappedEdgeFintype : Fintype (G.map f).edgeSet := Fintype.ofFinite _
local instance subgraphComparisonEmbeddedLargeEdgeFintype : Fintype H.edgeSet := Fintype.ofFinite _

/-- The genuine larger free FK law dominates the smaller free law on every
nonnegative increasing observable of the actual embedded original edges.
Only graph inclusion is assumed; added vertices, isolated vertices and all
configuration normalizations are handled by the proved transport theorems. -/
theorem embedded_free_expectation_le (q : Parameters) (B : Set V) (C : Set W)
    (F : Configuration G → ℝ) (hF0 : ∀ A, 0 ≤ F A) (hF : Monotone F) :
    expectation (law G q (BoundaryCondition.free B)) F ≤
      expectation (law H q (BoundaryCondition.free C))
        (fun A => F (embeddedConfigurationRestriction G H f hGH A)) := by
  have h := subgraph_expectation_le hGH q (BoundaryCondition.free C)
    (fun A => F ((isolatedExtensionConfigurationEquiv G f).symm A))
    (fun A => hF0 _) (hF.comp (isolatedExtensionConfigurationOrderIso G f).symm.monotone)
  rw [← law_isolatedExtension_map G f q B C, expectation_map] at h
  simpa only [Equiv.symm_apply_apply, embeddedConfigurationRestriction] using h

/-- The same statement for the actual marginal PMF on the smaller edge carrier. -/
theorem embedded_free_marginal_comparison (q : Parameters) (B : Set V) (C : Set W)
    (F : Configuration G → ℝ) (hF0 : ∀ A, 0 ≤ F A) (hF : Monotone F) :
    expectation (law G q (BoundaryCondition.free B)) F ≤
      expectation ((law H q (BoundaryCondition.free C)).map
        (embeddedConfigurationRestriction G H f hGH)) F := by
  rw [expectation_map]
  exact embedded_free_expectation_le G H f hGH q B C F hF0 hF

end EmbeddedVertices
end
end PottsDiscontinuity.FK
