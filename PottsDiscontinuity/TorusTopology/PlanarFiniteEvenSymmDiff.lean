/- Adapted from an earlier, unpublished formalization of the planar FK model by the same author.
Adaptation: Namespace and import relocation only. -/
module

public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Combinatorics.SimpleGraph.Matching
public import Mathlib.Data.Finset.SymmDiff
public import Mathlib.Tactic

@[expose] public section

namespace PottsDiscontinuity.TorusTopology.Planar.Medial

open SimpleGraph
open scoped symmDiff

private theorem card_symmDiff_add_two_card_inter {α : Type*} [DecidableEq α]
    (s t : Finset α) :
    (s ∆ t).card + 2 * (s ∩ t).card = s.card + t.card := by
  classical
  rw [Finset.symmDiff_def, Finset.card_union_of_disjoint]
  · have hst := Finset.card_sdiff_add_card_inter s t
    have hts := Finset.card_sdiff_add_card_inter t s
    rw [Finset.inter_comm] at hts
    omega
  · rw [Finset.disjoint_left]
    intro x hx hx'
    simp only [Finset.mem_sdiff] at hx hx'
    exact hx'.2 hx.1

theorem neighborFinset_symmDiff {V : Type*} [DecidableEq V]
    (G H : SimpleGraph V) [LocallyFinite G] [LocallyFinite H] [LocallyFinite (G ∆ H)] (v : V) :
    (G ∆ H).neighborFinset v = G.neighborFinset v ∆ H.neighborFinset v := by
  classical
  ext w
  rw [SimpleGraph.mem_neighborFinset, Finset.mem_symmDiff,
    SimpleGraph.mem_neighborFinset, SimpleGraph.mem_neighborFinset]
  simp [symmDiff_def, SimpleGraph.sup_adj, SimpleGraph.sdiff_adj]

theorem degree_even_symmDiff {V : Type*} [DecidableEq V]
    (G H : SimpleGraph V) [LocallyFinite G] [LocallyFinite H] [LocallyFinite (G ∆ H)]
    (hG : ∀ v, Even (G.degree v)) (hH : ∀ v, Even (H.degree v)) :
    ∀ v, Even ((G ∆ H).degree v) := by
  classical
  intro v
  rw [← SimpleGraph.card_neighborFinset_eq_degree, neighborFinset_symmDiff]
  have hg : Even (G.neighborFinset v).card := by
    rw [SimpleGraph.card_neighborFinset_eq_degree]
    exact hG v
  have hh : Even (H.neighborFinset v).card := by
    rw [SimpleGraph.card_neighborFinset_eq_degree]
    exact hH v
  have hcard := card_symmDiff_add_two_card_inter
    (G.neighborFinset v) (H.neighborFinset v)
  rcases hg with ⟨a, ha⟩
  rcases hh with ⟨b, hb⟩
  refine ⟨a + b - (G.neighborFinset v ∩ H.neighborFinset v).card, ?_⟩
  omega

end PottsDiscontinuity.TorusTopology.Planar.Medial
