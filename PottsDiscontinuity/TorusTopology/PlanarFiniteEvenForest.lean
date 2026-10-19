/- Adapted from an earlier, unpublished formalization of the planar FK model by the same author.
Adaptation: Namespace and import relocation only. -/
module

public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Combinatorics.SimpleGraph.Acyclic
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.Tactic

@[expose] public section

namespace PottsDiscontinuity.TorusTopology.Planar.Medial

open SimpleGraph

private theorem walk_support_reachable_from {V : Type*} (G : SimpleGraph V)
    {s u v : V} (hus : G.Reachable s u) (p : G.Walk u v) :
    ∀ x ∈ p.support, G.Reachable s x := by
  induction p with
  | nil =>
      intro x hx
      simp only [Walk.support_nil, List.mem_singleton] at hx
      subst x
      exact hus
  | @cons a b c hab p ih =>
      intro x hx
      simp only [Walk.support_cons, List.mem_cons] at hx
      rcases hx with rfl | hx
      · exact hus
      · exact ih (hus.trans hab.reachable) x hx

/-- A finite acyclic simple graph with even degree at every vertex has no edges. -/
theorem eq_bot_of_isAcyclic_even_degree
    {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hacyclic : G.IsAcyclic) (heven : ∀ v : V, Even (G.degree v)) :
    G = ⊥ := by
  classical
  rw [eq_bot_iff_forall_not_adj]
  intro u v huv
  let C : Type _ := {x : V // G.Reachable u x}
  let H : SimpleGraph C := G.induce (fun x : V => G.Reachable u x)
  let root : C := ⟨u, Reachable.refl u⟩
  have hclosed (x : C) : G.neighborSet x.1 ⊆ {y : V | G.Reachable u y} := by
    intro y hy
    rw [mem_neighborSet] at hy
    exact x.2.trans hy.reachable
  have hdegree (x : C) : H.degree x = G.degree x.1 := by
    dsimp [H, C]
    exact G.degree_induce_of_neighborSet_subset (hclosed x)
  have hconn : H.Connected := by
    apply H.connected_iff_exists_forall_reachable.mpr
    refine ⟨root, ?_⟩
    intro x
    rcases x.2 with ⟨p⟩
    have hsupport : ∀ y ∈ p.support, G.Reachable u y :=
      walk_support_reachable_from G (Reachable.refl u) p
    exact ⟨p.induce (fun y : V => G.Reachable u y) (fun y hy => hsupport y hy)⟩
  have hacyclicH : H.IsAcyclic := by
    dsimp [H, C]
    exact hacyclic.induce _
  have htree : H.IsTree := ⟨hconn, hacyclicH⟩
  have hne : v ≠ u := by
    intro h
    subst v
    exact huv.ne rfl
  let rv : C := ⟨v, huv.reachable⟩
  have hrootNe : root ≠ rv := by
    intro h
    exact hne (congrArg Subtype.val h).symm
  let : Nontrivial C := ⟨⟨root, rv, hrootNe⟩⟩
  obtain ⟨x, hx⟩ := htree.exists_vert_degree_one_of_nontrivial
  rw [hdegree] at hx
  obtain ⟨k, hk⟩ := heven x.1
  rw [hk] at hx
  omega

end PottsDiscontinuity.TorusTopology.Planar.Medial
