module

public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import Mathlib.Topology.Homotopy.Lifting
public import Mathlib.Topology.Homotopy.Path
public import PottsDiscontinuity.TorusExploration.MultiSeedClusterExploration
public import PottsDiscontinuity.TorusExploration.UnexploredEmbedding

/-! Restricting the planar unrolling to complements of several explored clusters. -/

@[expose] public section

namespace PottsDiscontinuity.TorusExploration
open Torus FK CorrLength
variable {N M : ℕ}
noncomputable section
open scoped Classical

/-- The entire seam-closed cylinder, including edges closed by a sample. -/
def fullCylinderGraph (hN : Even N) (hM : Even M) : SimpleGraph (FaceVertex N M true) :=
  diamondOpenGraph hN hM true (TorusRC.torusRCSeamClosed (openRCConfig N M))

/-- A finite FK cluster complement embeds after any one of its removed clusters
crosses the cylinder. The only bridge premises are literal graph equalities and
inclusions; no probability estimate or topological conclusion is assumed. -/
theorem multiComplement_embedding (hN : Even N) (hM : Even M)
    (hNp : 0 < N) (hMlarge : 1 < M) (G : SimpleGraph (FaceVertex N M true))
    (hG : G ≤ fullCylinderGraph hN hM) (C : Configuration G)
    (A : RCConfig N M)
    (hopen : openGraph G C=diamondOpenGraph hN hM true (TorusRC.torusRCSeamClosed A))
    (S : Finset (FaceVertex N M true)) {s t : FaceVertex N M true}
    (hs : s ∈ S) (hsbottom : s.val.2.val=0) (httop : t.val.2.val+1=M)
    (hst : ActualConnected G C s t) :
    ∃ f : actualMultiClusterComplementSet G S C ↪ RotatedVertex,
      (∀ w, (f w).val.2 = (w.val.val.2.val : ℤ)) ∧
      (G.induce (actualMultiClusterComplementSet G S C)).map f ≤ rotatedLattice := by
  have hst' : (diamondOpenGraph hN hM true (TorusRC.torusRCSeamClosed A)).Reachable s t := by
    rwa [← hopen]
  obtain ⟨f,hfy,hf⟩ := exists_unexploredCylinder_embedding hN hM hNp hMlarge hsbottom httop hst'
  let g := (actualMultiClusterComplementEmbedding G S C).trans f
  refine ⟨g,fun w => hfy w.val,?_⟩
  have hn (w : actualMultiClusterComplementSet G S C) :
      (diamondOpenGraph hN hM true (TorusRC.torusRCSeamClosed A)).connectedComponentMk w.val ≠
        (diamondOpenGraph hN hM true (TorusRC.torusRCSeamClosed A)).connectedComponentMk s := by
    intro he
    apply w.property
    refine ⟨s,hs,?_⟩
    have hh := SimpleGraph.ConnectedComponent.exact he.symm
    rwa [← hopen] at hh
  intro a b hab
  obtain ⟨u,v,huv,rfl,rfl⟩ := (SimpleGraph.map_adj _ _ _ _).1 hab
  apply hf u.val v.val
  have hfull := hG huv
  rw [fullCylinderGraph,diamondOpenGraph,SimpleGraph.fromEdgeSet_adj] at hfull
  obtain ⟨⟨e,he,hep⟩,hne⟩ := hfull
  have hrow : e.2.val ≠ 0 := by
    intro hz
    simp [TorusRC.torusRCSeamClosed,hz] at he
  have hend : ∀ b : Bool,
      (diamondOpenGraph hN hM true (TorusRC.torusRCSeamClosed A)).connectedComponentMk
        (faceEndpoint hN hM true e b) ≠
      (diamondOpenGraph hN hM true (TorusRC.torusRCSeamClosed A)).connectedComponentMk s := by
    rcases Sym2.eq_iff.1 hep with ⟨he0,he1⟩ | ⟨he0,he1⟩
    · change u.val = faceEndpoint hN hM true e false at he0
      change v.val = faceEndpoint hN hM true e true at he1
      intro b
      cases b
      · rw [← he0]; exact hn u
      · rw [← he1]; exact hn v
    · change u.val = faceEndpoint hN hM true e true at he0
      change v.val = faceEndpoint hN hM true e false at he1
      intro b
      cases b
      · rw [← he1]; exact hn v
      · rw [← he0]; exact hn u
  have hd : unexploredCylinderConfig hN hM A s e=true := by
    exact decide_eq_true ⟨hrow,hend⟩
  rw [diamondOpenGraph,SimpleGraph.fromEdgeSet_adj]
  exact ⟨⟨e,hd,hep⟩,hne⟩

end
end PottsDiscontinuity.TorusExploration
