module

public import PottsDiscontinuity.TorusTopology.PeriodicLatticeTurning

/-! The essential-loop turning classification, on the exact torus loop carrier
`Torus.Loop` used in Corollary 3.13. -/

@[expose] public section

namespace PottsDiscontinuity.TorusTopology
open Torus TorusLoops Finset
variable {N M : ℕ}

/-- A loop with nonzero homological winding has rotation number zero. -/
theorem loopRotationNumber_eq_zero_of_nonzero_winding
    (hN : Even N) (hM : Even M) (i : Fin N) (j : Fin M) (A : RCConfig N M)
    (q : Loop hN hM (rcSmoothing A))
    (hw : loopVertical (checkerArrows N M) (rcSmoothing A)
      (checkerArrows_compatible hN hM (rcSmoothing A)) j q ≠ 0 ∨
      loopSum (checkerArrows N M) (rcSmoothing A)
        (checkerArrows_compatible hN hM (rcSmoothing A))
        (PottsDiscontinuity.TorusLoops.horizontalCross i) q ≠ 0) :
    loopRotationNumber (checkerArrows N M) (rcSmoothing A)
      (checkerArrows_compatible hN hM (rcSmoothing A)) q = 0 := by
  obtain ⟨d,rfl⟩ := Quotient.exists_rep q
  let ω := checkerArrows N M
  let s := rcSmoothing A
  let h := checkerArrows_compatible hN hM s
  let f := loopMidpointPosition ω s h d
  let D := ((loopDeckDisplacement ω s h d i j).1+(loopDeckDisplacement ω s h d i j).2,
    (loopDeckDisplacement ω s h d i j).2-(loopDeckDisplacement ω s h d i j).1)
  have hadj : ∀ n, FK.squareLattice.Adj (f n) (f (n+1)) := loopMidpointPosition_adj ω s h d
  have hinj : Function.Injective f := loopMidpointPosition_injective_of_nonzero_winding ω s h d i j hw
  have hper : ∀ n, f (n+loopPeriod ω s h d)=f n+D :=
    loopMidpointPosition_add_period ω s h d i j
  have hD : D ≠ (0,0) := (rotated_loopDeckDisplacement_ne_zero_iff ω s h d i j).mpr hw
  have hz := periodic_lattice_turn_eq_zero f hadj hinj (loopPeriod ω s h d) D
    (loopPeriod_pos ω s h d) hD hper
  have hdir (n : ℕ) : sequenceCompass f hadj n =
      portCompass (midpointDirection s ((directedStep ω s h)^[n] d).val) := by
    exact squareDartCompass_eq_portCompass _ _
      (loopMidpointPosition_succ_direction ω s h d n)
  have hturn : (∑ n ∈ range (loopPeriod ω s h d),
      midpointQuarterTurn s ((directedStep ω s h)^[n] d).val) = 0 := by
    convert hz using 1
    apply Finset.sum_congr rfl
    intro n hn
    rw [hdir,hdir,portCompass_quarterTurn,Function.iterate_succ_apply',directedStep_val]
    rfl
  have ht := sum_period_midpointQuarterTurn_eq_four_mul_rotationNumber ω s h d
  rw [hturn] at ht
  dsimp [ω,s,h,directedLoopOf] at ht
  omega

end PottsDiscontinuity.TorusTopology
