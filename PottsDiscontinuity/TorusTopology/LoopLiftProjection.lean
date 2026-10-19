module

public import PottsDiscontinuity.TorusTopology.LoopOrbitLift
public import PottsDiscontinuity.TorusTopology.LiftedEdgeCover

/-! The ordered integer lift projects to the actual directed dart orbit on the torus
(under `Torus.stepPerm`) at every step. In particular its displacement is geometric,
rather than merely an abstract sum of two cocycles. -/

@[expose] public section

open PottsDiscontinuity.SixVertex
namespace PottsDiscontinuity.TorusTopology
open Torus TorusLoops TorusRC
variable {N M : ℕ}

lemma periodicCoordinate_add_one (hN : 0 < N) (z : ℤ) :
    periodicCoordinate hN (z+1) = nxt (periodicCoordinate hN z) := by
  have hh := periodicCoordinate_sub_one hN (z+1)
  rw [add_sub_cancel_right] at hh
  apply (finRotate N).symm.injective
  simpa only [prv,nxt,Equiv.symm_apply_apply] using hh.symm

/-- Integer nearest-neighbor steps project to precisely the medial step's vertex. -/
lemma loopLiftPosition_step_projection
    (hNp : 0 < N) (hMp : 0 < M) (s : Smoothing N M)
    (d : Dart N M) (z : ℤ × ℤ)
    (hx : periodicCoordinate hNp z.1 = d.1.1)
    (hy : periodicCoordinate hMp z.2 = d.1.2) :
    (periodicCoordinate hNp (z.1 + horizontalIncrement d),
     periodicCoordinate hMp (z.2 + verticalIncrement d)) = (stepPerm s d).1 := by
  rcases d with ⟨⟨i,j⟩,p⟩
  cases p <;>
    simp only [horizontalIncrement,verticalIncrement,add_zero,← sub_eq_add_neg,
      periodicCoordinate_sub_one,periodicCoordinate_add_one,hx,hy,
      stepPerm_apply,strandReverse,edgeReverse]

/-- At every time, the lift lies above the vertex of the actual torus dart. -/
theorem loopLiftPosition_projection (ω : ArrowConfig N M) (s : Smoothing N M)
    (h : CompatibleConfig ω s) (d : DirectedDart ω) (n : ℕ) :
    (periodicCoordinate (Fin.pos d.val.1.1) (loopLiftPosition ω s h d n).1,
     periodicCoordinate (Fin.pos d.val.1.2) (loopLiftPosition ω s h d n).2) =
      ((directedStep ω s h)^[n] d).val.1 := by
  induction n with
  | zero => simp [loopLiftPosition_zero,periodicCoordinate_nat]
  | succ n ih =>
    rw [loopLiftPosition_succ]
    have hx := congrArg Prod.fst ih
    have hy := congrArg Prod.snd ih
    have hh := loopLiftPosition_step_projection (Fin.pos d.val.1.1) (Fin.pos d.val.1.2)
      s (((directedStep ω s h)^[n] d).val) (loopLiftPosition ω s h d n) hx hy
    simpa only [Prod.fst_add,Prod.snd_add,Function.iterate_succ_apply',directedStep_val] using hh

/-- Distinct times before the least period represent distinct actual directed darts. -/
theorem loopOrbit_dart_injective (ω : ArrowConfig N M) (s : Smoothing N M)
    (h : CompatibleConfig ω s) (d : DirectedDart ω) :
    Function.Injective (fun k : Fin (loopPeriod ω s h d) =>
      ((directedStep ω s h)^[k.val] d).val) := by
  intro k l hh
  apply Fin.ext
  exact (Function.iterate_eq_iterate_iff_of_lt_minimalPeriod k.isLt l.isLt).mp
    (Subtype.ext hh)

/-- Keeping direction resolves a torus vertex visited by both smoothed strands. -/
theorem loopLiftPosition_port_injective (ω : ArrowConfig N M) (s : Smoothing N M)
    (h : CompatibleConfig ω s) (d : DirectedDart ω) :
    Function.Injective (fun k : Fin (loopPeriod ω s h d) =>
      (loopLiftPosition ω s h d k.val,((directedStep ω s h)^[k.val] d).val.2)) := by
  intro k l hh
  have hz := congrArg Prod.fst hh
  change loopLiftPosition ω s h d k.val = loopLiftPosition ω s h d l.val at hz
  have hp := congrArg Prod.snd hh
  apply loopOrbit_dart_injective ω s h d
  apply Prod.ext
  · rw [← loopLiftPosition_projection,← loopLiftPosition_projection,hz]
  · exact hp

end PottsDiscontinuity.TorusTopology
