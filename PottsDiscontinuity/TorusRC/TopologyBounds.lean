module

public import PottsDiscontinuity.TorusRC.CPrimeEstimate
public import PottsDiscontinuity.TorusRC.CylinderFiniteEnergy
public import PottsDiscontinuity.TorusTopology.BarrierEvent
public import PottsDiscontinuity.TorusTopology.CylinderCount

/-! # Quantitative reductions with the torus topology premises discharged

The premises that B ∩ C′ forces `U = 1` and that `U ≥ r` forces `r` distinct bottom-to-top
clusters after the seam row is closed are discharged by `TorusTopology.hBCU_proved` and
`TorusTopology.hUr_proved`. -/

@[expose] public section

namespace PottsDiscontinuity.TorusRC

open Torus CorrLength

variable {N M : ℕ}

/-- The proved implication B ∩ C′ ⇒ `U = 1` (`TorusTopology.hBCU_proved`) turns the full
corrected chain bound into an actual U=1 probability bound. No topological premise remains in
this finite-volume result. -/
theorem torusRCU_one_probability_ge_chain (hN : Even N) (hM : Even M)
    (hN4 : 4 ≤ N) (hM4 : 4 ≤ M) (hNp : 0 < N) (hMp : 0 < M)
    (hNdiv : 8 ∣ N) (q : Set.Ici (1 : ℝ)) (n : ℕ)
    (hn : 0 < n) (h8n : 8 * n ≤ N) (hNM : N / 2 < M) :
    (fkOpenEnergy (torusRCBridgeParameters q) ^ (2 * (N / 4 + 2 * n)) *
      liftedBoxFreeConnectionProbability (torusRCBridgeParameters q) rotatedLatticeOrigin
        (N / 4) rotatedLatticeOrigin (rotatedDiagonalSite n) ^ (M / (2 * n))) *
      torusRCProbability hN hM q (torusRCBarrier hNp hMp n) ≤
      torusRCProbability hN hM q {A | rcVerticalWinding hN hM ⟨0,hMp⟩ A = 1} := by
  apply (torusCPrime_mul_barrier_lower_bound hN hM hN4 hM4 hNp hMp hNdiv q n
    hn h8n hNM).trans
  apply torusRCProbability_mono
  intro A hA
  exact TorusTopology.hBCU_proved hN hM hNp hMp hNdiv n h8n hNM A hA.1 hA.2

/-- The proved statement that `U ≥ r` forces `r` distinct bottom-to-top clusters after the
seam row is closed (`TorusTopology.hUr_proved`) discharges the premise in the finite-energy
seam cut.
The remaining step for (3.16) is the cylinder exploration estimate. -/
theorem torusRCVerticalTail_close_seam_le_unconditional
    (hN : Even N) (hM : Even M) (hMp : 0 < M)
    (q : Set.Ici (1 : ℝ)) (r : ℕ) :
    (1 - (rcCriticalParameter q).val) ^ N *
        torusRCProbability hN hM q
          (torusRCVerticalTail hN hM ⟨0,hMp⟩ r) ≤
      torusRCProbability hN hM q
        (torusRCSeamClosedCrossingEvent hN hM r ∩ torusRCSeamRowClosed hMp) :=
  torusRCVerticalTail_close_seam_le hN hM hMp q r
    (TorusTopology.hUr_proved hN hM hMp r)

end PottsDiscontinuity.TorusRC
