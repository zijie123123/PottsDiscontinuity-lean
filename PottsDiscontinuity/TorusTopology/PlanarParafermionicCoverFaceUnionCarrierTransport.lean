/- Adapted from an earlier, unpublished formalization of the planar FK model by the same author.
Adaptation: Namespace and import relocation only. -/
module

public import PottsDiscontinuity.TorusTopology.PlanarParafermionicCoverFaceUnionConnectivity
public import PottsDiscontinuity.TorusTopology.PlanarParafermionicCoverFaceSetEdgeCount
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Tactic

@[expose] public section

namespace PottsDiscontinuity.TorusTopology.Planar.Medial

open PottsDiscontinuity.TorusTopology.Planar
open SimpleGraph

theorem parafermionicCoverFiniteFaceUnionGraph_edgeSet_eq_support {n : ℕ}
    (S : Finset (ParafermionicCoverFiniteFaceTopIndex n)) :
    (parafermionicCoverFiniteFaceUnionGraph S).edgeSet =
      (parafermionicCoverFiniteFaceSetEdgeSupport S :
        Set (Sym2 (ParafermionicCoverBoxVertex n))) := by
  classical
  ext e
  induction e using Sym2.inductionOn with
  | hf v w =>
      change (parafermionicCoverFiniteFaceUnionGraph S).Adj v w ↔
        s(v, w) ∈ (parafermionicCoverFiniteFaceSetEdgeSupport S : Set _)
      simp only [parafermionicCoverFiniteFaceUnionGraph,
        parafermionicCoverFiniteFaceSetEdgeSupport,
        parafermionicCoverFiniteFaceSelectedIncidentFaces,
        parafermionicCoverFiniteFaceIncidentFaces,
        Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.Nonempty, SimpleGraph.mem_edgeSet]
      simp only [and_comm]

private theorem parafermionicCoverFaceUnionSubgraph_support_subset {n : ℕ}
    (S : Finset (ParafermionicCoverFiniteFaceTopIndex n))
    (H : SimpleGraph (ParafermionicCoverBoxVertex n))
    (hH : H ≤ parafermionicCoverFiniteFaceUnionGraph S) :
    H.support ⊆ parafermionicCoverFiniteFaceUnionCarrier S := by
  intro v hv
  rcases hv with ⟨w, hvw⟩
  exact ⟨w, hH hvw⟩

theorem parafermionicCoverFiniteFaceUnionCarrier_induce_reachable_iff
    {n : ℕ} (S : Finset (ParafermionicCoverFiniteFaceTopIndex n))
    (H : SimpleGraph (ParafermionicCoverBoxVertex n))
    (hH : H ≤ parafermionicCoverFiniteFaceUnionGraph S)
    (v w : ParafermionicCoverBoxVertex n)
    (hv : v ∈ parafermionicCoverFiniteFaceUnionCarrier S)
    (hw : w ∈ parafermionicCoverFiniteFaceUnionCarrier S) :
    H.Reachable v w ↔
      (H.induce (parafermionicCoverFiniteFaceUnionCarrier S)).Reachable
        ⟨v, hv⟩ ⟨w, hw⟩ := by
  constructor
  · rintro ⟨p⟩
    have hsupp : ∀ x ∈ p.support,
        x ∈ parafermionicCoverFiniteFaceUnionCarrier S := by
      induction p with
      | nil =>
          intro x hx
          simp only [Walk.support_nil, List.mem_singleton] at hx
          subst x
          exact hv
      | @cons a b c hab tail ih =>
          intro x hx
          rw [Walk.support_cons] at hx
          rcases List.mem_cons.mp hx with hxa | hxt
          · subst x
            exact hv
          · have hb : b ∈ parafermionicCoverFiniteFaceUnionCarrier S :=
              ⟨a, (hH hab).symm⟩
            exact ih hb hw x hxt
    exact ⟨p.induce (parafermionicCoverFiniteFaceUnionCarrier S) hsupp⟩
  · rintro ⟨p⟩
    exact ⟨p.map (Embedding.induce
      (parafermionicCoverFiniteFaceUnionCarrier S)).toHom⟩

theorem parafermionicCoverFiniteFaceUnionCarrier_induce_edgeSet_card
    {n : ℕ} (S : Finset (ParafermionicCoverFiniteFaceTopIndex n))
    (H : SimpleGraph (ParafermionicCoverBoxVertex n))
    (hH : H ≤ parafermionicCoverFiniteFaceUnionGraph S) :
    Nat.card {e // e ∈ (H.induce
        (parafermionicCoverFiniteFaceUnionCarrier S)).edgeSet} =
      Nat.card {e // e ∈ H.edgeSet} := by
  classical
  have hsupp := parafermionicCoverFaceUnionSubgraph_support_subset S H hH
  rw [Nat.card_eq_fintype_card, ← SimpleGraph.edgeFinset_card,
    SimpleGraph.card_edgeFinset_induce_of_support_subset hsupp,
    SimpleGraph.edgeFinset_card, Nat.card_eq_fintype_card]

end PottsDiscontinuity.TorusTopology.Planar.Medial
