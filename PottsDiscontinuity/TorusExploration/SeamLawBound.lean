module

public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import Mathlib.Topology.Homotopy.Lifting
public import Mathlib.Topology.Homotopy.Path
public import PottsDiscontinuity.TorusExploration.ClosedSubgraphLaw
public import PottsDiscontinuity.TorusExploration.CylinderIndexedBridge
public import PottsDiscontinuity.TorusExploration.FiniteBoxComparison
public import PottsDiscontinuity.TorusRC.CylinderFiniteEnergy
public import PottsDiscontinuity.TorusRC.MeasureBridge

/-! The torus joint seam-closed event is bounded by the exact free cylinder law. -/

@[expose] public section

namespace PottsDiscontinuity.TorusExploration
open Torus TorusRC FK FK.FiniteProbability MeasureTheory
variable {N M : ℕ}
noncomputable section
open scoped Classical
local instance seamLawFullEdgeFintype (hN : Even N) (hM : Even M) :
    Fintype (fullDiamondGraph hN hM).edgeSet := Fintype.ofFinite _
local instance seamLawCylinderEdgeFintype (hN : Even N) (hM : Even M) :
    Fintype (fullCylinderGraph hN hM).edgeSet := Fintype.ofFinite _
local instance seamLawFullEdgeDecidableEq (hN : Even N) (hM : Even M) :
    DecidableEq (fullDiamondGraph hN hM).edgeSet := Classical.decEq _
attribute [local instance] configurationMeasurableSpace

lemma torusSeamClosed_mem_record (hN : Even N) (hM : Even M)
    (hN4 : 4 ≤ N) (hM4 : 4 ≤ M) (hMp : 0 < M) (A : RCConfig N M)
    (hA : A ∈ torusRCSeamRowClosed hMp) :
    torusRCConfigurationEquiv hN hM hN4 hM4 A ∈
      frozenStateEvent (subgraphRemovedEdges (fullCylinderGraph hN hM) (fullDiamondGraph hN hM))
        (closedSubgraphRecord (fullCylinderGraph hN hM) (fullDiamondGraph hN hM)) := by
  change _ ∩ _ = ∅
  apply Finset.eq_empty_iff_forall_notMem.2
  intro e he
  obtain ⟨heA,heR⟩ := Finset.mem_inter.1 he
  have hn := (mem_subgraphRemovedEdges (G := fullCylinderGraph hN hM) (H := fullDiamondGraph hN hM) e).1 heR
  obtain ⟨d,hd⟩ := (torusIndexedEdgeEquiv hN hM hN4 hM4).surjective e
  have hdA : A d=true := by
    apply (mem_torusRCConfigurationEquiv hN hM hN4 hM4 A d).1
    change torusIndexedEdgeEquiv hN hM hN4 hM4 d ∈ _
    rw [hd]
    exact heA
  have hrow : d.2.val ≠ 0 := by
    intro hz
    have hy : d.2=(⟨0,hMp⟩ : Fin M) := Fin.ext hz
    have hc := hA d.1
    rw [← hy] at hc
    exact Bool.noConfusion (hdA.symm.trans hc)
  apply hn
  rw [← hd]
  exact (indexedEdge_mem_cylinder_iff hN hM hN4 hM4 d).2 hrow

/-- No cylindrical comparison premise remains: closing the seam under the
periodic law induces precisely free boundary conditions on the cut graph. -/
theorem torus_seam_joint_le_cylinder (hN : Even N) (hM : Even M)
    (hN4 : 4 ≤ N) (hM4 : 4 ≤ M) (hMp : 0 < M) (q : Set.Ici (1 : ℝ)) (r : ℕ) :
    torusRCProbability hN hM q
      (torusRCSeamClosedCrossingEvent hN hM r ∩ torusRCSeamRowClosed hMp) ≤
    (measure (fullCylinderGraph hN hM) (torusRCBridgeParameters q) (BoundaryCondition.free ∅)
      {C | torusRCSeamClosedCylinderCrossings hN hM r
        (cylinderIndexedConfiguration hN hM hN4 hM4 C)}).toReal := by
  let G := fullCylinderGraph hN hM
  let H := fullDiamondGraph hN hM
  let hGH : G ≤ H := fullCylinderGraph_le_full hN hM
  let E : Set (Configuration G) := {C | torusRCSeamClosedCylinderCrossings hN hM r
    (cylinderIndexedConfiguration hN hM hN4 hM4 C)}
  let T := frozenStateEvent (subgraphRemovedEdges G H) (closedSubgraphRecord G H)
  let J := T ∩ (subgraphRemainderRead hGH) ⁻¹' E
  rw [torusRCProbability_eq_fk_image hN hM hN4 hM4 q]
  have hsub : torusRCConfigurationEquiv hN hM hN4 hM4 ''
      (torusRCSeamClosedCrossingEvent hN hM r ∩ torusRCSeamRowClosed hMp) ⊆ J := by
    rintro C ⟨A,⟨hcross,hclosed⟩,rfl⟩
    have hT := torusSeamClosed_mem_record hN hM hN4 hM4 hMp A hclosed
    refine ⟨hT,?_⟩
    have he := closedSubgraph_reconstruct hGH _ hT
    have hidx : cylinderIndexedConfiguration hN hM hN4 hM4
        (subgraphRemainderRead hGH (torusRCConfigurationEquiv hN hM hN4 hM4 A)) = A := by
      unfold cylinderIndexedConfiguration
      rw [he,Equiv.symm_apply_apply]
    change torusRCSeamClosedCylinderCrossings hN hM r _
    rw [hidx]
    have hseam : torusRCSeamClosed A=A := by
      funext e
      by_cases hz : e.2.val=0
      · have hy : e.2=(⟨0,hMp⟩ : Fin M) := Fin.ext hz
        simp only [torusRCSeamClosed,hz,ite_true]
        simpa only [← hy,Prod.eta] using (hclosed e.1).symm
      · simp [torusRCSeamClosed,hz]
    change torusRCSeamClosedCylinderCrossings hN hM r (torusRCSeamClosed A) at hcross
    rwa [hseam] at hcross
  refine (measureReal_mono hsub).trans ?_
  rw [Measure.real_def,fk_measureReal_eq_expectation,fk_measureReal_eq_expectation]
  exact closedSubgraph_joint_le hGH (torusRCBridgeParameters q) E

end
end PottsDiscontinuity.TorusExploration
