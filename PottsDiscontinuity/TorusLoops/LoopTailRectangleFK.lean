module

public import PottsDiscontinuity.TorusLoops.LoopTailSeamBound
public import PottsDiscontinuity.TorusLoops.RectangleLaw

/-!
# The corrected large-loop estimate under the free rectangle FK law

The cut-graph crossing event is transported to an event on rectangle FK
configurations through the seam-closed extension bijection.
-/

@[expose] public section

namespace PottsDiscontinuity.TorusLoops

open PottsDiscontinuity.Torus
open PottsDiscontinuity.TorusRC
open PottsDiscontinuity.FK

variable {N M : ℕ}

/-- The event that the seam-closed extension of a rectangle configuration has
at least `k` distinct horizontal cut-rectangle crossing components. -/
noncomputable def rectangleFKCrossingEvent (hN : Even N) (hM : Even M)
    (k : ℕ) : Set (Configuration (rectangleBaseGraph hN hM)) :=
  {C | k ≤ (rectangleCrossingComponents hN hM
    (rectangleRCConfigOfConfiguration hN hM C)).card}

private theorem rectangleSeamsClosed_iff_finset
    (A : RCConfig N M) :
    rectangleSeamsClosed A ↔
      ∀ v ∈ rectangleSeamIndices (N := N) (M := M), A v = false := by
  constructor
  · intro h v hv
    exact h v (Finset.mem_filter.mp hv).2
  · intro h v hv
    apply h v
    simp [rectangleSeamIndices, hv]

/-- On the closed seam fiber, the torus crossing event is exactly the lifted
rectangle FK crossing event. -/
theorem rectangleCrossings_closedEvent_eq_lift
    (hN : Even N) (hM : Even M) (k : ℕ) :
    hasAtLeastRectangleCrossings hN hM k ∩
        {A | ∀ v ∈ rectangleSeamIndices (N := N) (M := M), A v = false} =
      rectangleClosedLiftEvent hN hM (rectangleFKCrossingEvent hN hM k) := by
  classical
  ext A
  constructor
  · rintro ⟨hcross, hclosed⟩
    have hseam : rectangleSeamsClosed A :=
      (rectangleSeamsClosed_iff_finset A).2 hclosed
    refine ⟨hseam, ?_⟩
    change k ≤ (rectangleCrossingComponents hN hM
      (rectangleRCConfigOfConfiguration hN hM
        (rectangleConfigurationOfRC hN hM A))).card
    have hA := rectangleRCConfigOfConfiguration_rectangleConfigurationOfRC
      hN hM A (by
        intro v hv
        exact hseam v hv)
    have hcard := congrArg
      (fun B : RCConfig N M => (rectangleCrossingComponents hN hM B).card) hA
    rw [hcard]
    exact hcross
  · rintro ⟨hseam, hcross⟩
    refine ⟨?_, (rectangleSeamsClosed_iff_finset A).1 hseam⟩
    change k ≤ (rectangleCrossingComponents hN hM A).card
    change k ≤ (rectangleCrossingComponents hN hM
      (rectangleRCConfigOfConfiguration hN hM
        (rectangleConfigurationOfRC hN hM A))).card at hcross
    have hA := rectangleRCConfigOfConfiguration_rectangleConfigurationOfRC
      hN hM A (by
        intro v hv
        exact hseam v hv)
    have hcard := congrArg
      (fun B : RCConfig N M => (rectangleCrossingComponents hN hM B).card) hA
    rw [← hcard]
    exact hcross

/-- Corrected (3.17): a large winding-loop tail is bounded by a free-rectangle
FK event, with the exact seam finite-energy factor and rounded factor-two
crossing threshold. -/
theorem torusRCProbability_windingTail_le_rectangleFKCrossings
    (hN : Even N) (hM : Even M) (hNp : 0 < N) (hMp : 0 < M)
    (q : Set.Ici (1 : ℝ)) (m : ℕ) :
    (1 - (rcCriticalParameter q).val) ^
        (rectangleSeamIndices (N := N) (M := M)).card *
        phi_T_probability hN hM q (windingLoopTailEvent hN hM hNp hMp m) ≤
      rectangleFKEventProbability hN hM q
        (rectangleFKCrossingEvent hN hM ((m - 3 * N + 1) / 2)) := by
  have hfinite := torusRCProbability_windingTail_le_seamClosedCrossings
    hN hM hNp hMp q m
  rw [rectangleCrossings_closedEvent_eq_lift hN hM
    ((m - 3 * N + 1) / 2)] at hfinite
  exact hfinite.trans (phi_T_probability_rectangleClosedLift_le_rectangleFK
    hN hM q (rectangleFKCrossingEvent hN hM ((m - 3 * N + 1) / 2)))

end PottsDiscontinuity.TorusLoops
