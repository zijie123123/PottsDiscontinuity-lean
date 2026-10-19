module

public import PottsDiscontinuity.TorusTopology.MidpointCyclicTurning

/-! The contractible-loop turning classification, on the exact torus loop carrier
`Torus.Loop` used in Corollary 3.13. -/

@[expose] public section

namespace PottsDiscontinuity.TorusTopology
open Torus TorusLoops
variable {N M : ℕ}

/-- A loop with both homological windings zero has rotation number +1 or -1. -/
theorem loopRotationNumber_eq_pm_one_of_zero_winding
    (hN : Even N) (hM : Even M) (i : Fin N) (j : Fin M) (A : RCConfig N M)
    (q : Loop hN hM (rcSmoothing A))
    (hv : loopVertical (checkerArrows N M) (rcSmoothing A)
      (checkerArrows_compatible hN hM (rcSmoothing A)) j q = 0)
    (hh : loopSum (checkerArrows N M) (rcSmoothing A)
      (checkerArrows_compatible hN hM (rcSmoothing A))
      (PottsDiscontinuity.TorusLoops.horizontalCross i) q = 0) :
    loopRotationNumber (checkerArrows N M) (rcSmoothing A)
      (checkerArrows_compatible hN hM (rcSmoothing A)) q = 1 ∨
    loopRotationNumber (checkerArrows N M) (rcSmoothing A)
      (checkerArrows_compatible hN hM (rcSmoothing A)) q = -1 := by
  obtain ⟨d,rfl⟩ := Quotient.exists_rep q
  let ω := checkerArrows N M
  let s := rcSmoothing A
  let h := checkerArrows_compatible hN hM s
  have hp := closedLoopMidpointWalk_isCycle ω s h d i j hv hh
  have ht := squareWalkCyclicTurn_eq_four_or_neg_four _ hp
  rw [closedLoopMidpointWalk_cyclicTurn ω s h d i j hv hh] at ht
  dsimp [ω,s,h,directedLoopOf] at ht
  rcases ht with ht | ht
  · left; omega
  · right; omega

end PottsDiscontinuity.TorusTopology
