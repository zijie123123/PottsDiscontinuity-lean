/- Adapted from an earlier, unpublished formalization of the planar FK model by the same author.
Parameter generalization: independent 0 < p < 1 and 1 ≤ q, with no upper bound on q. -/
module

public import PottsDiscontinuity.FK.Marginal
public import Mathlib.Combinatorics.SimpleGraph.DeleteEdges
public import Mathlib.Data.Fintype.Card

/-!
# The same-vertex graph obtained by deleting the nonsampled edges

Deleting edges retains the entire original vertex type. Its configurations are
in exact correspondence with the previously defined remaining configurations;
actual open graphs, wired components, weights, and the full PMF agree.
-/

@[expose] public section

namespace PottsDiscontinuity.FK

noncomputable section

variable {V : Type*} (G : SimpleGraph V)

/-- Remove the specified original unordered edges, retaining every original vertex. -/
def edgeRestriction (R : Configuration G) : SimpleGraph V :=
  G.deleteEdges (openEdges G R)

theorem edgeRestriction_edgeSet (R : Configuration G) :
    (edgeRestriction G R).edgeSet = G.edgeSet \ openEdges G R :=
  G.edgeSet_deleteEdges _

theorem edgeRestriction_le (R : Configuration G) : edgeRestriction G R ≤ G :=
  G.deleteEdges_le _

/-- Membership is unchanged when an original edge is viewed as an unordered pair. -/
theorem coe_mem_openEdges_iff (R : Configuration G) (e : G.edgeSet) :
    e.val ∈ openEdges G R ↔ e ∈ R :=
  Subtype.val_injective.mem_set_image

/-- The edges of the deleted graph are exactly the original edges outside R. -/
def edgeRestrictionEdgeEquiv (R : Configuration G) :
    (edgeRestriction G R).edgeSet ≃ {e : G.edgeSet // e ∉ R} where
  toFun e := by
    have h : e.val ∈ G.edgeSet ∧ e.val ∉ openEdges G R := by
      simpa only [edgeRestriction_edgeSet, Set.mem_sdiff] using e.property
    exact ⟨⟨e.val, h.1⟩, fun he => h.2 ((coe_mem_openEdges_iff G R _).mpr he)⟩
  invFun e := ⟨e.val.val, by
    rw [edgeRestriction_edgeSet]
    exact ⟨e.val.property, fun he => e.property ((coe_mem_openEdges_iff G R _).mp he)⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Inclusion of a remaining graph edge into the original edge carrier. -/
def edgeRestrictionEdgeEmbedding (R : Configuration G) :
    (edgeRestriction G R).edgeSet ↪ G.edgeSet :=
  (edgeRestrictionEdgeEquiv G R).toEmbedding.trans (Function.Embedding.subtype _)

@[simp] theorem edgeRestrictionEdgeEmbedding_coe (R : Configuration G)
    (e : (edgeRestriction G R).edgeSet) :
    (edgeRestrictionEdgeEmbedding G R e).val = e.val := rfl

/-- The full configuration equivalence forgets only edge-membership proofs. -/
def edgeRestrictionConfigurationEquiv (R : Configuration G) :
    Configuration (edgeRestriction G R) ≃ RemainingConfiguration G R :=
  (edgeRestrictionEdgeEquiv G R).finsetCongr |>.trans
    ((Equiv.finsetSubtypeComm (fun e : G.edgeSet => e ∉ R)).trans
      (Equiv.subtypeEquivRight (fun A => by
        constructor
        · intro h
          exact Finset.disjoint_left.mpr h
        · intro h e he
          exact Finset.disjoint_left.mp h he)))

@[simp] theorem edgeRestrictionConfigurationEquiv_val (R : Configuration G)
    (A : Configuration (edgeRestriction G R)) :
    (edgeRestrictionConfigurationEquiv G R A).val = A.map (edgeRestrictionEdgeEmbedding G R) := by
  change (A.map (edgeRestrictionEdgeEquiv G R).toEmbedding).map
    (Function.Embedding.subtype _) = _
  exact Finset.map_map _ _ _

/-- The actual sampled-edge order is preserved in both directions. -/
theorem edgeRestrictionConfigurationEquiv_le_iff (R : Configuration G)
    (A B : Configuration (edgeRestriction G R)) :
    (edgeRestrictionConfigurationEquiv G R A).val ⊆
      (edgeRestrictionConfigurationEquiv G R B).val ↔ A ⊆ B := by
  rw [edgeRestrictionConfigurationEquiv_val, edgeRestrictionConfigurationEquiv_val]
  exact Finset.map_subset_map

/-- The configuration bijection is an order isomorphism for open-edge inclusion. -/
def edgeRestrictionConfigurationOrderIso (R : Configuration G) :
    Configuration (edgeRestriction G R) ≃o RemainingConfiguration G R where
  toEquiv := edgeRestrictionConfigurationEquiv G R
  map_rel_iff' := edgeRestrictionConfigurationEquiv_le_iff G R _ _

/-- No open edge is added, contracted, or relabeled geometrically. -/
theorem openEdges_edgeRestriction (R : Configuration G)
    (A : Configuration (edgeRestriction G R)) :
    openEdges (edgeRestriction G R) A =
      openEdges G (edgeRestrictionConfigurationEquiv G R A).val := by
  simp only [openEdges, edgeRestrictionConfigurationEquiv_val, Finset.coe_map, Set.image_image]
  rfl

/-- The two configurations have literally the same open graph on all original vertices. -/
theorem openGraph_edgeRestriction (R : Configuration G)
    (A : Configuration (edgeRestriction G R)) :
    openGraph (edgeRestriction G R) A =
      openGraph G (edgeRestrictionConfigurationEquiv G R A).val := by
  rw [openGraph, openGraph, openEdges_edgeRestriction]

theorem componentSetoid_edgeRestriction (ξ : BoundaryCondition V) (R : Configuration G)
    (A : Configuration (edgeRestriction G R)) :
    componentSetoid (edgeRestriction G R) ξ A =
      componentSetoid G ξ (edgeRestrictionConfigurationEquiv G R A).val := by
  rw [componentSetoid, componentSetoid, openGraph_edgeRestriction]

theorem componentCount_edgeRestriction [Finite V] (ξ : BoundaryCondition V)
    (R : Configuration G) (A : Configuration (edgeRestriction G R)) :
    componentCount (edgeRestriction G R) ξ A =
      componentCount G ξ (edgeRestrictionConfigurationEquiv G R A).val := by
  rw [componentCount, componentCount, componentSetoid_edgeRestriction]

@[simp] theorem card_edgeRestrictionConfigurationEquiv (R : Configuration G)
    (A : Configuration (edgeRestriction G R)) :
    (edgeRestrictionConfigurationEquiv G R A).val.card = A.card := by
  rw [edgeRestrictionConfigurationEquiv_val, Finset.card_map]

/-- The exact number of genuinely sampled edges, on the same original vertex type. -/
theorem edgeRestriction_card [Finite V] (R : Configuration G) :
    Nat.card (edgeRestriction G R).edgeSet = Nat.card G.edgeSet - R.card := by
  classical
  let : Fintype G.edgeSet := Fintype.ofFinite _
  rw [Nat.card_congr (edgeRestrictionEdgeEquiv G R), Nat.card_eq_fintype_card,
    Fintype.card_subtype_compl, Nat.card_eq_fintype_card, Fintype.card_coe]

/-- The ordinary FK weight on the actual deleted graph is the existing reduced
weight. No prewiring premise is needed for this exact change of carrier. -/
theorem weight_edgeRestriction [Finite V] (q : Parameters) (ξ : BoundaryCondition V)
    (R : Configuration G) (A : Configuration (edgeRestriction G R)) :
    weight (edgeRestriction G R) q ξ A =
      remainingWeight G q ξ R (edgeRestrictionConfigurationEquiv G R A) := by
  rw [weight, remainingWeight, edgeRestriction_card,
    card_edgeRestrictionConfigurationEquiv, componentCount_edgeRestriction]

section Finite

variable [Finite V]
local instance edgeRestrictionOriginalEdgeFintype : Fintype G.edgeSet := Fintype.ofFinite _
local instance edgeRestrictionRemainingEdgeFintype (R : Configuration G) :
    Fintype (edgeRestriction G R).edgeSet := Fintype.ofFinite _
local instance edgeRestrictionConfigurationFintype (R : Configuration G) :
    Fintype (RemainingConfiguration G R) := Fintype.ofFinite _

/-- The entire FK law on the same-vertex deleted graph transports to the exact
remaining-edge law, permitting proved finite-graph inequalities to be reused. -/
theorem law_edgeRestriction_map (q : Parameters) (ξ : BoundaryCondition V)
    (R : Configuration G) :
    (law (edgeRestriction G R) q ξ).map (edgeRestrictionConfigurationEquiv G R) =
      remainingLaw G q ξ R := by
  unfold law remainingLaw
  exact FiniteProbability.pmf_map_equiv_of_weight_eq (edgeRestrictionConfigurationEquiv G R)
    _ _ _ _ (weight_edgeRestriction G q ξ R)

end Finite
end
end PottsDiscontinuity.FK
