module

public import PottsDiscontinuity.Torus.NetEuler
public import PottsDiscontinuity.TorusLoops.LoopClusterProjection

/-! Boundary-loop chains span the primal conserved chains whenever the
horizontal displacement vanishes on all primal cycles. This replaces the
planar-lift separation argument by the proved exact cellular radical theorem. -/

@[expose] public section

open Finset PottsDiscontinuity.SixVertex
namespace PottsDiscontinuity.TorusTopology
open Torus TorusLoops
variable {N M : ℕ}
noncomputable section

/-- Transport a boundary-component function to the actual medial-loop carrier. -/
def loopBoundaryLabel (hN : Even N) (hM : Even M) (A : RCConfig N M)
    (F : RibbonBoundaryComponent hN hM A → ℚ) : Loop hN hM (rcSmoothing A) → ℚ :=
  Quotient.lift (fun d => F (ribbonBoundaryOf hN hM A d)) (fun _ _ h => by
    apply congrArg F
    apply Quotient.sound
    rwa [ribbonBoundary_eq_directedStep])

/-- Expand a genuine cellular face boundary into individual medial-loop shadows. -/
theorem ribbonFaceBoundary_eq_sum_loopBoundaryCycles
    (hN : Even N) (hM : Even M) (A : RCConfig N M)
    (F : RibbonBoundaryComponent hN hM A → ℚ) :
    ribbonFaceBoundary hN hM A F =
      ∑ q : Loop hN hM (rcSmoothing A),
        loopBoundaryLabel hN hM A F q • (loopBoundaryCycle hN hM A q).val := by
  classical
  funext e
  change F (ribbonBoundaryOf hN hM A (ribbonEndEquiv hN hM (e.val,true))) -
      F (ribbonBoundaryOf hN hM A (ribbonEndEquiv hN hM (e.val,false))) = _
  simp only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul,loopBoundaryCycle,
    ribbonFaceBoundary,LinearMap.coe_mk,AddHom.coe_mk,loopBoundaryFunction_corner,
    mul_sub,mul_ite,mul_one,mul_zero,Finset.sum_sub_distrib,
    Finset.sum_ite_eq,Finset.mem_univ,ite_true]
  rfl

/-- Vanishing vertical winding on all loops kills the vertical displacement
of every actual cellular boundary. -/
theorem boundary_vertical_displacement_zero_of_loops_zero
    (hN : Even N) (hM : Even M) (j : Fin M) (A : RCConfig N M)
    (hzero : ∀ q : Loop hN hM (rcSmoothing A),
      loopVertical _ _ (checkerArrows_compatible hN hM (rcSmoothing A)) j q = 0)
    (f : diamondCycleSpace hN hM A) (hf : f ∈ ribbonBoundarySpace hN hM A) :
    diamondVerticalDisplacement A f.val = 0 := by
  classical
  obtain ⟨F,hF⟩ := hf
  have hF' : ribbonFaceBoundary hN hM A F = f.val := congrArg Subtype.val hF
  rw [← hF',ribbonFaceBoundary_eq_sum_loopBoundaryCycles,diamondVerticalDisplacement]
  simp only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul]
  rw [Finset.sum_comm,← Finset.sum_neg_distrib]
  apply Finset.sum_eq_zero
  intro q _
  rw [← Finset.mul_sum]
  have hq : -(∑ e, (loopBoundaryCycle hN hM A q).val e) = 0 := by
    change diamondVerticalDisplacement A (loopBoundaryCycle hN hM A q).val = 0
    rw [loopBoundaryCycle_displacement_y,loop_vertical_displacement _ _ _ j q,hzero q,mul_zero]
    rfl
  have hq' : (∑ e, (loopBoundaryCycle hN hM A q).val e) = 0 := neg_eq_zero.1 hq
  rw [hq',mul_zero,neg_zero]

/-- When all primal cycles are vertically aligned, each is an actual ribbon
boundary, by the exact intersection-radical theorem. -/
theorem mem_boundary_of_horizontal_displacement_zero
    (hN : Even N) (hM : Even M) (hNp : 0 < N) (hMp : 0 < M)
    (A : RCConfig N M)
    (hX : ∀ f : diamondCycleSpace hN hM A, diamondHorizontalDisplacement A f.val = 0)
    (f : diamondCycleSpace hN hM A) : f ∈ ribbonBoundarySpace hN hM A := by
  apply mem_ribbonBoundarySpace_of_intersection_zero hN hM A f
  intro g
  apply (ribbonIntersection_eq_zero_iff_windingDeterminant_zero hN hM hNp hMp A f g).2
  simp only [diamondWindingDeterminant,hX f,hX g,zero_mul,mul_zero,sub_self]

/-- A nonzero vertical primal cycle with no horizontal primal homology forces
an actual vertically winding medial loop. -/
theorem exists_vertical_loop_of_aligned_vertical_cycle
    (hN : Even N) (hM : Even M) (hNp : 0 < N) (hMp : 0 < M)
    (j : Fin M) (A : RCConfig N M)
    (hX : ∀ f : diamondCycleSpace hN hM A, diamondHorizontalDisplacement A f.val = 0)
    (hY : ∃ f : diamondCycleSpace hN hM A, diamondVerticalDisplacement A f.val ≠ 0) :
    ∃ q : Loop hN hM (rcSmoothing A),
      loopVertical _ _ (checkerArrows_compatible hN hM (rcSmoothing A)) j q ≠ 0 := by
  classical
  by_contra hn
  push Not at hn
  obtain ⟨f,hf⟩ := hY
  exact hf (boundary_vertical_displacement_zero_of_loops_zero hN hM j A hn f
    (mem_boundary_of_horizontal_displacement_zero hN hM hNp hMp A hX f))

end
end PottsDiscontinuity.TorusTopology
