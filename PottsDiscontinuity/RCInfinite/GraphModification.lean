module

public import PottsDiscontinuity.RCInfinite.OpeningPaths

@[expose] public section

open Set

namespace PottsDiscontinuity.RCInfinite
open FK
noncomputable section
open scoped Classical

/-- If new edges have both endpoints in a finite set, every new infinite
component contains an old infinite component. -/
theorem infinite_component_contains_old
    {V : Type*} {G H : SimpleGraph V} (hGH : G ≤ H) (S : Finset V)
    (hnew : ∀ x y, H.Adj x y → ¬G.Adj x y → x ∈ S ∧ y ∈ S)
    (x : V) (hinf : {y | H.Reachable x y}.Infinite) :
    ∃ z, H.Reachable x z ∧ {y | G.Reachable z y}.Infinite := by
  have hwalk {u v : V} (w : H.Walk u v) :
      ∃ z, (z = u ∨ z ∈ S) ∧ G.Reachable z v := by
    induction w with
    | nil => exact ⟨_, Or.inl rfl, .refl _⟩
    | @cons u v t huv w ih =>
      obtain ⟨z, hz, hzt⟩ := ih
      rcases hz with hz | hz
      · subst z
        by_cases hold : G.Adj u v
        · exact ⟨u, Or.inl rfl, hold.reachable.trans hzt⟩
        · exact ⟨v, Or.inr (hnew u v huv hold).2, hzt⟩
      · exact ⟨z, Or.inr hz, hzt⟩
  let T : Finset V := (insert x S).filter fun z => H.Reachable x z
  have hcover : {y | H.Reachable x y} ⊆ ⋃ z ∈ (T : Set V), {y | G.Reachable z y} := by
    intro y hxy
    obtain ⟨w⟩ := hxy
    obtain ⟨z, hz, hzy⟩ := hwalk w
    have hxz : H.Reachable x z := w.reachable.trans (hzy.mono hGH).symm
    refine mem_iUnion.mpr ⟨z, mem_iUnion.mpr ⟨?_, hzy⟩⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_insert.mpr hz, hxz⟩
  by_contra! hnone
  have hfinite : (⋃ z ∈ (T : Set V), {y | G.Reachable z y}).Finite := by
    apply T.finite_toSet.biUnion
    intro z hz
    exact hnone z (Finset.mem_filter.mp hz).2
  exact hinf (hfinite.subset hcover)

def edgeEndpoints (F : Finset Edge) : Finset LatticeVertex :=
  F.biUnion fun e => e.val.toFinset

theorem opening_new_edge_endpoints (F : Finset Edge) (ω : LatticeConfiguration)
    (x y : LatticeVertex)
    (hnew : (rcInfiniteOpenGraph (setEdges F (fun _ => true) ω)).Adj x y)
    (hold : ¬(rcInfiniteOpenGraph ω).Adj x y) :
    x ∈ edgeEndpoints F ∧ y ∈ edgeEndpoints F := by
  obtain ⟨he, hω⟩ := (rcInfiniteOpenGraph_adj _ x y).mp hnew
  have hF : (⟨s(x, y), he⟩ : Edge) ∈ F := by
    by_contra hF
    apply hold
    apply (rcInfiniteOpenGraph_adj _ x y).mpr
    exact ⟨he, by simpa only [setEdges, hF, ite_false] using hω⟩
  constructor
  · exact Finset.mem_biUnion.mpr ⟨⟨s(x, y), he⟩, hF, by simp [Sym2.toFinset_mk_eq]⟩
  · exact Finset.mem_biUnion.mpr ⟨⟨s(x, y), he⟩, hF, by simp [Sym2.toFinset_mk_eq]⟩

theorem opening_infinite_component_contains_old (F : Finset Edge)
    (ω : LatticeConfiguration) (x : LatticeVertex)
    (hx : setEdges F (fun _ => true) ω ∈ infiniteAt x) :
    ∃ z, (rcInfiniteOpenGraph (setEdges F (fun _ => true) ω)).Reachable x z ∧
      ω ∈ infiniteAt z :=
  infinite_component_contains_old (opening_graph_mono F ω) (edgeEndpoints F)
    (opening_new_edge_endpoints F ω) x hx

end
end PottsDiscontinuity.RCInfinite
