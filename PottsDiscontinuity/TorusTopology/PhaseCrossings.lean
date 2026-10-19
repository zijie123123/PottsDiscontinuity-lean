module

public import PottsDiscontinuity.TorusTopology.CylinderCrossing
public import PottsDiscontinuity.TorusTopology.LiftedPotentials
public import PottsDiscontinuity.TorusTopology.PhaseFlux

/-! Each nonzero modular phase flux forces a genuine bottom-to-top cylinder
component. Distinct phases cannot belong to the same seam-closed cluster. -/

@[expose] public section

open Finset PottsDiscontinuity.SixVertex
namespace PottsDiscontinuity.TorusTopology
open Torus TorusRC
variable {N M b : ℕ}
noncomputable section

/-- The seam-closed cylinder is a subgraph of the original primal graph. -/
theorem seamClosed_graph_le (hN : Even N) (hM : Even M) (A : RCConfig N M) :
    diamondOpenGraph hN hM true (torusRCSeamClosed A) ≤ diamondOpenGraph hN hM true A := by
  intro u v huv
  rw [diamondOpenGraph,SimpleGraph.fromEdgeSet_adj] at huv ⊢
  obtain ⟨⟨e,he,hep⟩,hne⟩ := huv
  have hy : e.2.val ≠ 0 := by intro hy; simp [torusRCSeamClosed,hy] at he
  have hAe : A e=true := by simpa only [torusRCSeamClosed,hy,ite_false] using he
  exact ⟨⟨e,hAe,hep⟩,hne⟩

/-- A winding phase is constant along an actual seam-closed component. -/
theorem winding_phase_eq_of_cylinder_reachable
    (hN : Even N) (hM : Even M) (A : RCConfig N M)
    (c : (diamondOpenGraph hN hM true A).ConnectedComponent)
    (g : FaceVertex N M true → ZMod b)
    (hg : ∀ e : OpenDiamondEdge A, diamondEdgeCluster hN hM A e=c →
      g (faceEndpoint hN hM true e.val true)-g (faceEndpoint hN hM true e.val false) =
        if e.val.2.val=0 then -1 else 0)
    {u v : FaceVertex N M true}
    (hu : (diamondOpenGraph hN hM true A).connectedComponentMk u=c)
    (hr : (diamondOpenGraph hN hM true (torusRCSeamClosed A)).Reachable u v) : g u=g v := by
  have hadj {w z : FaceVertex N M true}
      (hw : (diamondOpenGraph hN hM true A).connectedComponentMk w=c)
      (h : (diamondOpenGraph hN hM true (torusRCSeamClosed A)).Adj w z) : g w=g z := by
    rw [diamondOpenGraph,SimpleGraph.fromEdgeSet_adj] at h
    obtain ⟨⟨e,he,hep⟩,_⟩ := h
    have hy : e.2.val ≠ 0 := by intro hy; simp [torusRCSeamClosed,hy] at he
    have hAe : A e=true := by simpa only [torusRCSeamClosed,hy,ite_false] using he
    rcases Sym2.eq_iff.1 hep with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    · have hv := hg ⟨e,hAe⟩ hw
      simp only [hy,ite_false] at hv
      exact (sub_eq_zero.1 hv).symm
    · have hc : diamondEdgeCluster hN hM A ⟨e,hAe⟩=c :=
        (SimpleGraph.ConnectedComponent.sound (diamond_endpoints_reachable hN hM A e hAe)).trans hw
      have hv := hg ⟨e,hAe⟩ hc
      simp only [hy,ite_false] at hv
      exact sub_eq_zero.1 hv
  rw [SimpleGraph.reachable_iff_reflTransGen] at hr
  induction hr with
  | refl => rfl
  | @tail w z hr hwz ih =>
    have hreach : (diamondOpenGraph hN hM true A).Reachable u w :=
      ((SimpleGraph.reachable_iff_reflTransGen u w).2 hr).mono (seamClosed_graph_le hN hM A)
    have hw : (diamondOpenGraph hN hM true A).connectedComponentMk w=c :=
      (SimpleGraph.ConnectedComponent.sound hreach).symm.trans hu
    exact ih.trans (hadj hw hwz)

/-- Every phase of a chain with winding b has a bottom-to-top cylinder cluster
inside its original primal component. -/
theorem exists_cylinder_crossing_at_each_phase
    (hN : Even N) (hM : Even M) (hMp : 0 < M) (A : RCConfig N M) (hb : 0 < b)
    (c : (diamondOpenGraph hN hM true A).ConnectedComponent)
    (g : FaceVertex N M true → ZMod b)
    (hg : ∀ e : OpenDiamondEdge A, diamondEdgeCluster hN hM A e=c →
      g (faceEndpoint hN hM true e.val true)-g (faceEndpoint hN hM true e.val false) =
        if e.val.2.val=0 then -1 else 0)
    (f : diamondCycleSpace hN hM A) (hs : SupportedOnDiamondCluster hN hM A c f)
    (hw : diamondWindingY A f.val = (b : ℚ)) (k : ZMod b) :
    ∃ u : FaceVertex N M true, u.val.2.val=0 ∧
      (diamondOpenGraph hN hM true A).connectedComponentMk u=c ∧
        g u=k ∧ cylinderReachesTop hN hM A u := by
  classical
  by_contra hn
  let P : FaceVertex N M true → ℚ := fun u =>
    if g u=k ∧ cylinderReachesTop hN hM A u then 1 else 0
  have hp := diamondBoundary_pairing hN hM A P f.val
  rw [f.property] at hp
  simp only [Pi.zero_apply,mul_zero,Finset.sum_const_zero] at hp
  have hterm (e : OpenDiamondEdge A) :
      diamondCoboundary hN hM A P e * f.val e =
        if e.val.2.val=0 ∧ g (faceEndpoint hN hM true e.val false)=k+1 then f.val e else 0 := by
    by_cases hc : diamondEdgeCluster hN hM A e=c
    · have he := hg e hc
      by_cases hy : e.val.2.val=0
      · simp only [hy,ite_true] at he
        have hfy : (faceEndpoint hN hM true e.val false).val.2.val=0 := by
          rw [faceEndpoint_false_y]; exact hy
        have hty : (faceEndpoint hN hM true e.val true).val.2.val+1=M := by
          obtain ⟨m,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hMp.ne'
          have hz : e.val.2=0 := Fin.ext hy
          have hep : (faceEndpoint hN hM true e.val true).val.2=prv e.val.2 := by
            cases hcheck : checker e.val <;> simp [faceEndpoint,faceEndpointRaw,hcheck]
          rw [hep,hz,prv_zero]
          simp
        have ht : cylinderReachesTop hN hM A (faceEndpoint hN hM true e.val true) :=
          ⟨_,hty,SimpleGraph.Reachable.refl _⟩
        have hfalse : P (faceEndpoint hN hM true e.val false)=0 := by
          dsimp [P]
          split_ifs with h
          · exact (hn ⟨_,hfy,hc,h.1,h.2⟩).elim
          · rfl
        have heq : g (faceEndpoint hN hM true e.val true)=k ↔
            g (faceEndpoint hN hM true e.val false)=k+1 := by
          constructor
          · intro h; rw [h] at he; linear_combination -he
          · intro h; rw [h] at he; linear_combination he
        rw [diamondCoboundary_apply,hfalse]
        simp only [P,ht,and_true,heq,sub_zero,ite_mul,one_mul,zero_mul,hy,true_and]
      · simp only [hy,ite_false] at he
        have hg0 := sub_eq_zero.1 he
        have hopen : torusRCSeamClosed A e.val=true := by simp [torusRCSeamClosed,hy,e.property]
        have hr := diamond_endpoints_reachable hN hM (torusRCSeamClosed A) e.val hopen
        have htop : cylinderReachesTop hN hM A (faceEndpoint hN hM true e.val true) ↔
            cylinderReachesTop hN hM A (faceEndpoint hN hM true e.val false) := by
          constructor
          · rintro ⟨v,hv,hvR⟩; exact ⟨v,hv,hr.trans hvR⟩
          · rintro ⟨v,hv,hvR⟩; exact ⟨v,hv,hr.symm.trans hvR⟩
        simp [diamondCoboundary_apply,P,hg0,propext htop,hy]
    · rw [hs e hc]
      simp
  have hz : phaseFlux hN hM A g (k+1) f.val=0 := by
    unfold phaseFlux
    rw [Finset.sum_filter]
    simp_rw [← hterm]
    exact hp.symm
  rw [phaseFlux_eq_neg_one hN hM A hb c g hg f hs hw] at hz
  norm_num at hz

end
end PottsDiscontinuity.TorusTopology
