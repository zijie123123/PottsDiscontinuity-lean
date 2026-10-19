/- Adapted from an earlier, unpublished formalization of the planar FK model by the same author.
Generalized to independent interior edge probability and cluster weight at least one. -/
module

public import PottsDiscontinuity.FK.EdgeConditional

/-!
# Exact one-edge FK conditional probabilities

With every other edge fixed, the open probability is p if the endpoints are
already connected after wiring and p/(p+(1-p)q) otherwise. These are ratios
of the actual positive singleton probabilities on the two-configuration event.
They are increasing with the other open edges, and obey uniform finite-energy
bounds. No association or multi-edge stochastic domination is asserted here.
-/

@[expose] public section

namespace PottsDiscontinuity.FK

variable {V : Type*} [Finite V] {G : SimpleGraph V} [DecidableEq G.edgeSet]

/-- The extra factor q records the single component lost upon opening. -/
theorem weight_insert_balance_of_not_related (q : Parameters) (ξ : BoundaryCondition V)
    (A : Configuration G) {u v : V} (huv : G.Adj u v)
    (he : (⟨s(u,v), G.mem_edgeSet.mpr huv⟩ : G.edgeSet) ∉ A)
    (hne : ¬ (componentSetoid G ξ A).r u v) :
    (1-edgeParameter q) * q.val * weight G q ξ (insert ⟨s(u,v),G.mem_edgeSet.mpr huv⟩ A) =
      edgeParameter q * weight G q ξ A := by
  have hc : A.card + 1 ≤ Nat.card G.edgeSet := by
    let : Fintype G.edgeSet := Fintype.ofFinite _
    rw [Nat.card_eq_fintype_card, ← Finset.card_insert_of_notMem he]
    exact Finset.card_le_univ _
  have hec : Nat.card G.edgeSet - A.card = Nat.card G.edgeSet - (A.card+1) + 1 := by omega
  have hcomp := componentCount_insert_of_not_related ξ A huv hne
  rw [weight, weight, Finset.card_insert_of_notMem he, ← hcomp, hec,
    pow_succ, pow_succ, pow_succ]
  ring

/-- The denominator in the distinct-component conditional probability is positive. -/
theorem edge_conditional_denominator_pos (q : Parameters) :
    0 < edgeParameter q + (1 - edgeParameter q) * q.val :=
  add_pos (edgeParameter_pos q)
    (mul_pos (one_sub_edgeParameter_pos q) (clusterWeight_pos q))

/-- The exact open probability for two distinct endpoint components. -/
theorem configurationProbability_pair_ratio_of_not_related (q : Parameters)
    (ξ : BoundaryCondition V) (A : Configuration G) {u v : V} (huv : G.Adj u v)
    (he : (⟨s(u,v), G.mem_edgeSet.mpr huv⟩ : G.edgeSet) ∉ A)
    (hne : ¬ (componentSetoid G ξ A).r u v) :
    configurationProbability G q ξ (insert ⟨s(u,v),G.mem_edgeSet.mpr huv⟩ A) /
      (configurationProbability G q ξ A +
        configurationProbability G q ξ (insert ⟨s(u,v),G.mem_edgeSet.mpr huv⟩ A)) =
      (edgeParameter q / (edgeParameter q + (1 - edgeParameter q) * q.val)) := by
  have h : (1 - edgeParameter q) * q.val *
      configurationProbability G q ξ (insert ⟨s(u,v),G.mem_edgeSet.mpr huv⟩ A) =
      edgeParameter q * configurationProbability G q ξ A := by
    unfold configurationProbability
    rw [← mul_div_assoc, ← mul_div_assoc,
      weight_insert_balance_of_not_related q ξ A huv he hne]
  apply (div_eq_iff (add_pos (configurationProbability_pos G q ξ A)
    (configurationProbability_pos G q ξ _)).ne').mpr
  rw [div_mul_eq_mul_div]
  apply (eq_div_iff (edge_conditional_denominator_pos q).ne').mpr
  nlinarith only [h]

/-- The two possible conditional values are ordered for the full source range q>=1. -/
theorem lower_edge_conditional_le_parameter (q : Parameters) :
    (edgeParameter q / (edgeParameter q + (1 - edgeParameter q) * q.val)) ≤ edgeParameter q := by
  apply (div_le_iff₀ (edge_conditional_denominator_pos q)).mpr
  have hq := mul_le_mul_of_nonneg_left q.property (one_sub_edgeParameter_pos q).le
  have hp := edgeParameter_pos q
  nlinarith

/-- Uniform nontrivial lower and upper bounds on the actual two-state conditional. -/
theorem configurationProbability_pair_ratio_bounds (q : Parameters)
    (ξ : BoundaryCondition V) (A : Configuration G) {u v : V} (huv : G.Adj u v)
    (he : (⟨s(u,v), G.mem_edgeSet.mpr huv⟩ : G.edgeSet) ∉ A) :
    (edgeParameter q / (edgeParameter q + (1 - edgeParameter q) * q.val)) ≤
      configurationProbability G q ξ (insert ⟨s(u,v),G.mem_edgeSet.mpr huv⟩ A) /
        (configurationProbability G q ξ A +
          configurationProbability G q ξ (insert ⟨s(u,v),G.mem_edgeSet.mpr huv⟩ A)) ∧
    configurationProbability G q ξ (insert ⟨s(u,v),G.mem_edgeSet.mpr huv⟩ A) /
        (configurationProbability G q ξ A +
          configurationProbability G q ξ (insert ⟨s(u,v),G.mem_edgeSet.mpr huv⟩ A)) ≤
      edgeParameter q := by
  by_cases h : (componentSetoid G ξ A).r u v
  · rw [configurationProbability_pair_ratio_of_related q ξ A huv he h]
    exact ⟨lower_edge_conditional_le_parameter q, le_rfl⟩
  · rw [configurationProbability_pair_ratio_of_not_related q ξ A huv he h]
    exact ⟨le_rfl, lower_edge_conditional_le_parameter q⟩

end PottsDiscontinuity.FK
