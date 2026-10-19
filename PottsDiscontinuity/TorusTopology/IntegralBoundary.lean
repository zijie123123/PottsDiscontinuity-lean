module

public import PottsDiscontinuity.Torus.NetEuler
public import PottsDiscontinuity.TorusLoops.LoopClusterProjection

/-! Integral saturation of the actual ribbon face boundary map. Its edge
coefficients are differences, so flooring a rational face potential preserves
an integer boundary chain exactly. -/

@[expose] public section

namespace PottsDiscontinuity.TorusTopology
open Torus TorusLoops
variable {N M : ℕ}
noncomputable section

/-- An integer-valued rational ribbon boundary has an integer face potential.
This is an exact saturation statement, not a rational approximation. -/
theorem exists_int_face_potential_of_integral_boundary
    (hN : Even N) (hM : Even M) (A : RCConfig N M)
    (f : diamondCycleSpace hN hM A) (hf : f ∈ ribbonBoundarySpace hN hM A)
    (hint : ∀ e : OpenDiamondEdge A, ∃ z : ℤ, f.val e = z) :
    ∃ F : RibbonBoundaryComponent hN hM A → ℤ,
      ribbonFaceBoundary hN hM A (fun q => (F q : ℚ)) = f.val := by
  obtain ⟨F,hF⟩ := hf
  refine ⟨fun q => ⌊F q⌋,?_⟩
  funext e
  obtain ⟨z,hz⟩ := hint e
  have he := congrFun (congrArg Subtype.val hF) e
  change F (ribbonBoundaryOf hN hM A (ribbonEndEquiv hN hM (e.val,true))) -
    F (ribbonBoundaryOf hN hM A (ribbonEndEquiv hN hM (e.val,false))) = f.val e at he
  rw [hz] at he
  have he' : F (ribbonBoundaryOf hN hM A (ribbonEndEquiv hN hM (e.val,true))) =
      F (ribbonBoundaryOf hN hM A (ribbonEndEquiv hN hM (e.val,false))) + z := by linarith
  change (⌊F (ribbonBoundaryOf hN hM A (ribbonEndEquiv hN hM (e.val,true)))⌋ : ℤ) -
    (⌊F (ribbonBoundaryOf hN hM A (ribbonEndEquiv hN hM (e.val,false)))⌋ : ℤ) = f.val e
  rw [he',Int.floor_add_intCast,hz]
  push_cast
  ring

/-- A nonzero vertical boundary loop makes the entire primal intersection
pairing vanish, even when its primitive slope has a horizontal component. -/
theorem all_cycles_mem_boundary_of_vertical_loop
    (hN : Even N) (hM : Even M) (hNp : 0 < N) (hMp : 0 < M)
    (j : Fin M) (A : RCConfig N M) (q : Loop hN hM (rcSmoothing A))
    (hq : loopVertical _ _ (checkerArrows_compatible hN hM (rcSmoothing A)) j q ≠ 0)
    (f : diamondCycleSpace hN hM A) : f ∈ ribbonBoundarySpace hN hM A := by
  let b := loopBoundaryCycle hN hM A q
  have hb : b ∈ ribbonBoundarySpace hN hM A := ⟨loopBoundaryFunction hN hM A q,rfl⟩
  have hy : diamondVerticalDisplacement A b.val ≠ 0 := by
    rw [show b = loopBoundaryCycle hN hM A q from rfl,
      loopBoundaryCycle_displacement_y,loop_vertical_displacement _ _ _ j q]
    exact_mod_cast mul_ne_zero (by exact_mod_cast hMp.ne' : (M : ℤ) ≠ 0) hq
  have hd (g : diamondCycleSpace hN hM A) : diamondWindingDeterminant A b.val g.val = 0 :=
    (ribbonIntersection_eq_zero_iff_windingDeterminant_zero hN hM hNp hMp A b g).1
      (ribbonIntersection_zero_of_mem_boundary hN hM A b g hb)
  apply mem_ribbonBoundarySpace_of_intersection_zero hN hM A f
  intro g
  apply (ribbonIntersection_eq_zero_iff_windingDeterminant_zero hN hM hNp hMp A f g).2
  have hbf := hd f
  have hbg := hd g
  unfold diamondWindingDeterminant at hbf hbg ⊢
  apply (mul_eq_zero.mp (show diamondVerticalDisplacement A b.val *
      (diamondHorizontalDisplacement A f.val * diamondVerticalDisplacement A g.val -
        diamondVerticalDisplacement A f.val * diamondHorizontalDisplacement A g.val) = 0 by
    calc
      _ = diamondVerticalDisplacement A f.val *
          (diamondHorizontalDisplacement A b.val * diamondVerticalDisplacement A g.val -
            diamondVerticalDisplacement A b.val * diamondHorizontalDisplacement A g.val) -
          diamondVerticalDisplacement A g.val *
          (diamondHorizontalDisplacement A b.val * diamondVerticalDisplacement A f.val -
            diamondVerticalDisplacement A b.val * diamondHorizontalDisplacement A f.val) := by ring
      _ = 0 := by rw [hbf,hbg,mul_zero,mul_zero,sub_self])).resolve_left hy

end
end PottsDiscontinuity.TorusTopology
