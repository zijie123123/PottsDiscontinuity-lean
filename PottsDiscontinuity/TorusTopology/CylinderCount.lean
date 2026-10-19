module

public import PottsDiscontinuity.TorusTopology.LoopPhaseCrossings

/-! T3: U at least r gives r distinct bottom-to-top clusters in the exact
seam-closed cylinder. Positive loop phases retain every winding multiplicity. -/

@[expose] public section

open PottsDiscontinuity.SixVertex
namespace PottsDiscontinuity.TorusTopology
open Torus TorusRC TorusLoops
variable {N M : ℕ}
noncomputable section

/-- Every positive loop-phase slot supplies a distinct cylinder crossing
component. There are exactly U slots. -/
theorem exists_crossing_family_indexed_by_vertical_phases
    (hN : Even N) (hM : Even M) (hMp : 0 < M) (A : RCConfig N M) :
    ∃ x : VerticalPhaseIndex hN hM ⟨0,hMp⟩ A → FaceVertex N M true,
      (∀ s, (x s).val.2.val=0 ∧ cylinderReachesTop hN hM A (x s)) ∧
      Function.Injective (fun s =>
        (diamondOpenGraph hN hM true (torusRCSeamClosed A)).connectedComponentMk (x s)) := by
  classical
  let P := positiveVerticalLoops hN hM ⟨0,hMp⟩ A
  have hex (q : P) := cylinder_crossings_of_positive_vertical_loop hN hM hMp ⟨0,hMp⟩ A q.val
    (Finset.mem_filter.1 q.property).2
  choose x hx using hex
  let X (s : VerticalPhaseIndex hN hM ⟨0,hMp⟩ A) := x s.1 s.2
  refine ⟨X,fun s => ⟨((hx s.1).1 s.2).1,((hx s.1).1 s.2).2.2⟩,?_⟩
  rintro ⟨q,i⟩ ⟨r,k⟩ he
  have hr : (diamondOpenGraph hN hM true (torusRCSeamClosed A)).Reachable (x q i) (x r k) :=
    SimpleGraph.ConnectedComponent.eq.1 he
  have hro := SimpleGraph.ConnectedComponent.sound (hr.mono (seamClosed_graph_le hN hM A))
  have hqr : q=r := positive_vertical_loops_primalCluster_injective hN hM ⟨0,hMp⟩ A
    (((hx q).1 i).2.1.symm.trans (hro.trans ((hx r).1 k).2.1))
  subst r
  have hik : i=k := by
    by_contra hn
    exact (hx q).2 i k hn hr
  subst k
  rfl

/-- T3 on the exact cylinder event `TorusRC.torusRCSeamClosedCylinderCrossings`. Only seam
edges are closed; no additional finite-energy modification or endpoint placement is assumed. -/
theorem seamClosedCylinderCrossings_of_le_U
    (hN : Even N) (hM : Even M) (hMp : 0 < M) (r : ℕ) (A : RCConfig N M)
    (hr : r ≤ rcVerticalWinding hN hM ⟨0,hMp⟩ A) :
    torusRCSeamClosedCylinderCrossings hN hM r (torusRCSeamClosed A) := by
  classical
  obtain ⟨x,hx,hinj⟩ := exists_crossing_family_indexed_by_vertical_phases hN hM hMp A
  obtain ⟨e⟩ : Nonempty (Fin r ↪ VerticalPhaseIndex hN hM ⟨0,hMp⟩ A) :=
    Function.Embedding.nonempty_of_card_le (by rw [Fintype.card_fin,card_verticalPhaseIndex]; exact hr)
  refine ⟨fun i => x (e i),fun i => (hx (e i)).1,?_,?_⟩
  · intro i
    exact (hx (e i)).2
  · intro i j hij hreach
    exact hij (e.injective (hinj (SimpleGraph.ConnectedComponent.sound hreach)))

/-- The exact quantitative topology contract `TorusRC.hUr` is discharged for every r. -/
theorem hUr_proved (hN : Even N) (hM : Even M) (hMp : 0 < M) (r : ℕ) :
    hUr hN hM hMp r :=
  fun A hr => seamClosedCylinderCrossings_of_le_U hN hM hMp r A hr

end
end PottsDiscontinuity.TorusTopology
