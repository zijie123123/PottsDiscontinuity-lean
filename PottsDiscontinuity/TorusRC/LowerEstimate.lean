module

public import PottsDiscontinuity.TorusRC.BarrierLower
public import PottsDiscontinuity.TorusRC.TopologyBounds

/-! # The complete finite-volume lower estimate for U=1 -/

@[expose] public section

namespace PottsDiscontinuity.TorusRC

open Torus CorrLength

noncomputable local instance lowerEstimateBoxEdgeFintype (c : RotatedVertex) (R : ℕ) :
    Fintype (liftedBoxGraph c R).edgeSet := Fintype.ofFinite _

/-- All finite-volume ingredients of (3.15), with the topological premise that B ∩ C′
forces `U = 1` discharged (`TorusTopology.hBCU_proved`, via `TorusRC/TopologyBounds.lean`).
Only the uniform rectangle-crossing estimate h319 remains a premise. -/
theorem torusRCU_one_lower_of_h319 (q : Set.Ici (1 : ℝ)) (hh319 : h319 q) :
    ∃ c : ℝ, 0 < c ∧ c ≤ 1 ∧ ∀ (N M n : ℕ) (hN : Even N) (hM : Even M)
      (hN4 : 4 ≤ N) (hM4 : 4 ≤ M) (hNdiv : 8 ∣ N) (hn : 2 ≤ n)
      (h8nN : 8*n ≤ N) (h4nM : 4*n ≤ M) (hNM : N/2 < M),
      let _hNp : 0 < N := by omega
      let hMp : 0 < M := by omega
      (fkOpenEnergy (torusRCBridgeParameters q) ^ (2*(N/4+2*n)) *
        liftedBoxFreeConnectionProbability (torusRCBridgeParameters q) rotatedLatticeOrigin
          (N/4) rotatedLatticeOrigin (rotatedDiagonalSite n) ^ (M/(2*n))) *
        ((torusRCSurgeryEnergy q ^ (2*n+N) *
          (c/(9*(n:ℝ)^2)) ^ ((M:ℝ)/(n:ℝ))) / q.val^2) ≤
      torusRCProbability hN hM q {A | rcVerticalWinding hN hM ⟨0,hMp⟩ A = 1} := by
  obtain ⟨c,hc,hc1,hB⟩ := barrier_source_lower_of_h319 q hh319
  refine ⟨c,hc,hc1,?_⟩
  intro N M n hN hM hN4 hM4 hNdiv hn h8nN h4nM hNM
  have hb := hB N M n hN hM hN4 hM4 hn (by omega) h4nM
  have hnonneg : 0 ≤ fkOpenEnergy (torusRCBridgeParameters q) ^ (2*(N/4+2*n)) *
      liftedBoxFreeConnectionProbability (torusRCBridgeParameters q) rotatedLatticeOrigin
        (N/4) rotatedLatticeOrigin (rotatedDiagonalSite n) ^ (M/(2*n)) := by
    apply mul_nonneg (pow_nonneg (fkOpenEnergy_pos _).le _)
    apply pow_nonneg
    exact torusRCFiberEventProbability_nonneg _ _
  exact (mul_le_mul_of_nonneg_left hb hnonneg).trans
    (torusRCU_one_probability_ge_chain hN hM hN4 hM4 (by omega) (by omega)
      hNdiv q n (by omega) h8nN hNM)

end PottsDiscontinuity.TorusRC
