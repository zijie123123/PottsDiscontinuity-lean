/- Adapted from an earlier, unpublished formalization of the planar FK model by the same author.
Namespaces/imports adapted to the shared FK library. -/
module

public import Mathlib.Combinatorics.SimpleGraph.DegreeSum
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

@[expose] public section

namespace PottsDiscontinuity.FK

/-- In a finite graph, an odd total degree on `B` forces a path from `B` to `T`
when every vertex outside the two sets has even degree. -/
theorem exists_reachable_between_of_odd_degree_sum
    {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableEq V] [DecidableRel G.Adj] (B T : Finset V)
    (hdisj : Disjoint B T)
    (heven : ∀ v, v ∉ (B ∪ T) → Even (G.degree v))
    (hodd : Odd (∑ v ∈ B, G.degree v)) :
    ∃ b ∈ B, ∃ t ∈ T, G.Reachable b t := by
  classical
  by_contra hgoal
  have hno (b : V) (hb : b ∈ B) (t : V) (ht : t ∈ T) :
      ¬ G.Reachable b t := by
    intro hreach
    by_cases hbt : b = t
    · subst t
      exact (Finset.disjoint_left.mp hdisj) hb ht
    · exact hgoal ⟨b, hb, t, ht, hreach⟩
  let S : Finset V := Finset.univ.filter fun v => ∃ b ∈ B, G.Reachable b v
  have memS (v : V) : v ∈ S ↔ ∃ b ∈ B, G.Reachable b v := by
    simp [S]
  have hBsub : B ⊆ S := by
    intro b hb
    rw [memS]
    exact ⟨b, hb, SimpleGraph.Reachable.refl b⟩
  have hclosed {u v : V} (hu : u ∈ S) (hadj : G.Adj u v) : v ∈ S := by
    rw [memS] at hu ⊢
    rcases hu with ⟨b, hb, hreach⟩
    exact ⟨b, hb, hreach.trans hadj.reachable⟩
  have hSdisj : Disjoint S T := by
    apply Finset.disjoint_left.mpr
    intro t htS htT
    rcases (memS t).mp htS with ⟨b, hb, hreach⟩
    exact hno b hb t htT hreach
  have hdegreeSumS : Even (∑ v ∈ S, G.degree v) := by
    let Ss : Set V := (S : Set V)
    let subtypeFintype : Fintype {x // x ∈ Ss} := Subtype.fintype _
    have hsum :
        (∑ v ∈ S, G.degree v) =
          ∑ v : {x // x ∈ Ss}, (G.induce Ss).degree v := by
      have hatt : S.attach = (Finset.univ : Finset {x // x ∈ Ss}) := by
        ext v
        simp [Ss]
      rw [← Finset.sum_attach]
      rw [hatt]
      apply Finset.sum_congr rfl
      intro v hv
      have hneighbors : G.neighborSet (v : V) ⊆ Ss := by
        intro z hz
        exact hclosed v.property ((G.mem_neighborSet (v : V) z).mp hz)
      exact (G.degree_induce_of_neighborSet_subset hneighbors).symm
    rw [hsum, (G.induce Ss).sum_degrees_eq_twice_card_edges]
    exact ⟨(G.induce Ss).edgeFinset.card, by omega⟩
  have hevenSum : ∀ U : Finset V,
      (∀ v ∈ U, Even (G.degree v)) → Even (∑ v ∈ U, G.degree v) := by
    intro U
    induction U using Finset.induction_on with
    | empty => simp
    | @insert x U hx ih =>
        intro h
        rw [Finset.sum_insert hx]
        exact (h x (Finset.mem_insert_self x U)).add
          (ih (fun v hv => h v (Finset.mem_insert_of_mem hv)))
  have houtside : Even (∑ v ∈ (S \ B), G.degree v) := by
    apply hevenSum
    intro v hv
    have hvS : v ∈ S := (Finset.mem_sdiff.mp hv).1
    have hvB : v ∉ B := (Finset.mem_sdiff.mp hv).2
    have hvT : v ∉ T := by
      intro ht
      exact (Finset.disjoint_left.mp hSdisj) hvS ht
    exact heven v (by simp [hvB, hvT])
  have hdecomp :
      (∑ v ∈ (S \ B), G.degree v) + (∑ v ∈ B, G.degree v) =
        ∑ v ∈ S, G.degree v :=
    Finset.sum_sdiff hBsub (f := fun v => G.degree v)
  have hsumEven : Even ((∑ v ∈ (S \ B), G.degree v) +
      (∑ v ∈ B, G.degree v)) := by
    rw [hdecomp]
    exact hdegreeSumS
  have hB_even : Even (∑ v ∈ B, G.degree v) := by
    rcases houtside with ⟨m, hm⟩
    rcases hsumEven with ⟨n, hn⟩
    refine ⟨n - m, ?_⟩
    omega
  have hnotEven : ¬ Even (∑ v ∈ B, G.degree v) := by
    intro he
    rcases hodd with ⟨k, hk⟩
    rcases he with ⟨j, hj⟩
    omega
  exact hnotEven hB_even

end PottsDiscontinuity.FK
