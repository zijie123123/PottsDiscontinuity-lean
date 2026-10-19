module

public import PottsDiscontinuity.FK.SubgraphComparison

/-! Restriction of actual connectivity to an induced union of open clusters. -/

@[expose] public section

namespace PottsDiscontinuity.TorusExploration
open FK
variable {V : Type*} [Finite V] (G : SimpleGraph V)
noncomputable section
open scoped Classical
local instance inducedConnectivityEdgeFintype : Fintype G.edgeSet := Fintype.ofFinite _
local instance inducedConnectivityEdgeDecidableEq : DecidableEq G.edgeSet := Classical.decEq _

/-- The literal inclusion of an induced vertex set. -/
def inducedVertexEmbedding (T : Set V) : T ↪ V := ⟨Subtype.val,Subtype.val_injective⟩

omit [Finite V] in
lemma inducedVertexGraph_le (T : Set V) : (G.induce T).map (inducedVertexEmbedding T) ≤ G := by
  intro a b hab
  obtain ⟨u,v,huv,rfl,rfl⟩ := (SimpleGraph.map_adj _ _ _ _).1 hab
  exact huv

omit [Finite V] in
lemma inducedRestriction_open_adj (T : Set V) (A : Configuration G) (u v : T) :
    (openGraph (G.induce T) (embeddedConfigurationRestriction (G.induce T) G
      (inducedVertexEmbedding T) (inducedVertexGraph_le G T) A)).Adj u v ↔
      (openGraph G A).Adj u.val v.val := by
  rw [openGraph_adj,openGraph_adj]
  constructor
  · rintro ⟨e,he,hep⟩
    refine ⟨embeddedEdgeEmbedding _ _ _ _ e,
      (mem_embeddedConfigurationRestriction _ _ _ _ _ _).1 he,?_⟩
    change Sym2.map Subtype.val e.val=s(u.val,v.val)
    rw [hep]
    rfl
  · rintro ⟨e,he,hep⟩
    have hg : G.Adj u.val v.val := G.mem_edgeSet.1 (hep ▸ e.property)
    let d : (G.induce T).edgeSet := ⟨s(u,v),hg⟩
    refine ⟨d,?_,rfl⟩
    apply (mem_embeddedConfigurationRestriction (G.induce T) G (inducedVertexEmbedding T)
      (inducedVertexGraph_le G T) A d).2
    have hed : embeddedEdgeEmbedding (G.induce T) G (inducedVertexEmbedding T)
        (inducedVertexGraph_le G T) d=e := by
      apply Subtype.ext
      exact hep.symm
    rwa [hed]

omit [Finite V] in
/-- If the vertex set is closed under actual open steps, every actual path
between its vertices is already a path of the restricted configuration. -/
theorem actualConnected_inducedRestriction (T : Set V) (A : Configuration G)
    (hT : ∀ a ∈ T, ∀ b, (openGraph G A).Adj a b → b ∈ T) (u v : T) :
    ActualConnected (G.induce T) (embeddedConfigurationRestriction (G.induce T) G
      (inducedVertexEmbedding T) (inducedVertexGraph_le G T) A) u v ↔
        ActualConnected G A u.val v.val := by
  constructor
  · rintro ⟨p⟩
    exact ⟨p.map {toFun := Subtype.val,map_rel' := fun h => (inducedRestriction_open_adj G T A _ _).1 h}⟩
  · rintro ⟨p⟩
    have lift {a b : V} (p : (openGraph G A).Walk a b) (ha : a ∈ T) (hb : b ∈ T) :
        (openGraph (G.induce T) (embeddedConfigurationRestriction (G.induce T) G
          (inducedVertexEmbedding T) (inducedVertexGraph_le G T) A)).Reachable ⟨a,ha⟩ ⟨b,hb⟩ := by
      induction p with
      | nil => exact SimpleGraph.Reachable.refl _
      | @cons a b c hab p ih =>
        have hb' := hT a ha b hab
        exact ((inducedRestriction_open_adj G T A ⟨a,ha⟩ ⟨b,hb'⟩).2 hab).reachable.trans (ih hb' hb)
    exact lift p u.property v.property

end
end PottsDiscontinuity.TorusExploration
