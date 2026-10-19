module

public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import Mathlib.Topology.Homotopy.Lifting
public import Mathlib.Topology.Homotopy.Path
public import PottsDiscontinuity.TorusExploration.ComplementEmbedding
public import PottsDiscontinuity.TorusRC.IndexedGraphBridge

/-! Exact original-edge bridge for the full seam-closed cylinder. -/

@[expose] public section

namespace PottsDiscontinuity.TorusExploration
open Torus TorusRC FK
variable {N M : ℕ}
noncomputable section
open scoped Classical

lemma fullCylinderGraph_le_full (hN : Even N) (hM : Even M) :
    fullCylinderGraph hN hM ≤ fullDiamondGraph hN hM := by
  intro u v huv
  rw [fullCylinderGraph,diamondOpenGraph,SimpleGraph.fromEdgeSet_adj] at huv
  obtain ⟨⟨e,_,he⟩,hne⟩ := huv
  rw [fullDiamondGraph,diamondOpenGraph,SimpleGraph.fromEdgeSet_adj]
  exact ⟨⟨e,rfl,he⟩,hne⟩

lemma indexedEdge_mem_cylinder_iff (hN : Even N) (hM : Even M)
    (hN4 : 4 ≤ N) (hM4 : 4 ≤ M) (e : Fin N × Fin M) :
    (torusIndexedEdgeEmbedding hN hM hN4 hM4 e).val ∈ (fullCylinderGraph hN hM).edgeSet ↔
      e.2.val ≠ 0 := by
  rw [fullCylinderGraph,diamondOpenGraph,SimpleGraph.edgeSet_fromEdgeSet]
  constructor
  · rintro ⟨⟨d,hd,hpair⟩,_⟩
    have heq : d=e := (torusIndexedEdgeEmbedding hN hM hN4 hM4).injective (Subtype.ext hpair.symm)
    subst d
    intro he0
    simp [TorusRC.torusRCSeamClosed,he0] at hd
  · intro he0
    refine ⟨⟨e,?_,rfl⟩,?_⟩
    · simp [TorusRC.torusRCSeamClosed,he0,openRCConfig]
    · intro hd
      have hneq := (fullDiamondGraph hN hM).mem_edgeSet.1
        (torusIndexedEdgeEmbedding hN hM hN4 hM4 e).property
      exact hneq.ne (Sym2.mk_isDiag_iff.1 (Sym2.mem_diagSet.1 hd))

/-- The indexed sample of the genuine finite cylinder FK configuration,
with its absent seam edges closed. -/
def cylinderIndexedConfiguration (hN : Even N) (hM : Even M)
    (hN4 : 4 ≤ N) (hM4 : 4 ≤ M) (C : Configuration (fullCylinderGraph hN hM)) : RCConfig N M :=
  (torusRCConfigurationEquiv hN hM hN4 hM4).symm
    (subgraphConfigurationEmbedding (fullCylinderGraph_le_full hN hM) C)

lemma cylinderIndexedConfiguration_seam (hN : Even N) (hM : Even M)
    (hN4 : 4 ≤ N) (hM4 : 4 ≤ M) (C : Configuration (fullCylinderGraph hN hM))
    (e : Fin N × Fin M) (he : e.2.val=0) :
    cylinderIndexedConfiguration hN hM hN4 hM4 C e=false := by
  cases hc : cylinderIndexedConfiguration hN hM hN4 hM4 C e with
  | false => rfl
  | true =>
    have hm := (mem_torusRCConfigurationEquiv hN hM hN4 hM4
      (cylinderIndexedConfiguration hN hM hN4 hM4 C) e).2 hc
    change torusIndexedEdgeEmbedding hN hM hN4 hM4 e ∈
      torusRCConfigurationEquiv hN hM hN4 hM4
        ((torusRCConfigurationEquiv hN hM hN4 hM4).symm _) at hm
    rw [Equiv.apply_symm_apply] at hm
    obtain ⟨d,_,hd⟩ := Finset.mem_map.1 hm
    have hv := congrArg Subtype.val hd
    have hcyl : (torusIndexedEdgeEmbedding hN hM hN4 hM4 e).val ∈
        (fullCylinderGraph hN hM).edgeSet := hv ▸ d.property
    exact ((indexedEdge_mem_cylinder_iff hN hM hN4 hM4 e).1 hcyl he).elim

lemma cylinderIndexedConfiguration_eq_seamClosed (hN : Even N) (hM : Even M)
    (hN4 : 4 ≤ N) (hM4 : 4 ≤ M) (C : Configuration (fullCylinderGraph hN hM)) :
    TorusRC.torusRCSeamClosed (cylinderIndexedConfiguration hN hM hN4 hM4 C) =
      cylinderIndexedConfiguration hN hM hN4 hM4 C := by
  funext e
  by_cases he : e.2.val=0
  · simp [TorusRC.torusRCSeamClosed,he,cylinderIndexedConfiguration_seam hN hM hN4 hM4 C e he]
  · simp [TorusRC.torusRCSeamClosed,he]

lemma openGraph_cylinderIndexedConfiguration (hN : Even N) (hM : Even M)
    (hN4 : 4 ≤ N) (hM4 : 4 ≤ M) (C : Configuration (fullCylinderGraph hN hM)) :
    openGraph (fullCylinderGraph hN hM) C = diamondOpenGraph hN hM true
      (TorusRC.torusRCSeamClosed (cylinderIndexedConfiguration hN hM hN4 hM4 C)) := by
  rw [cylinderIndexedConfiguration_eq_seamClosed,← openGraph_simpleConfiguration,
    simpleConfiguration_eq_torusRCConfigurationEquiv hN hM hN4 hM4]
  unfold cylinderIndexedConfiguration
  rw [Equiv.apply_symm_apply,openGraph_subgraphConfigurationEmbedding]

end
end PottsDiscontinuity.TorusExploration
