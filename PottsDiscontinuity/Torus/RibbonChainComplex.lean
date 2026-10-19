module

public import PottsDiscontinuity.Torus.RibbonFaceBoundary

/-!
# The boundary-of-boundary identity

Incidence pairing is discrete integration by parts. Reindexing corner sums by the
boundary permutation then proves that every capped ribbon face has zero divergence.
-/

@[expose] public section

open Finset Matrix PottsDiscontinuity.SixVertex

namespace PottsDiscontinuity.Torus

variable {N M : ℕ}

theorem diamondBoundary_pairing (hN : Even N) (hM : Even M) (A : RCConfig N M)
    (g : FaceVertex N M true → ℚ) (f : OpenDiamondEdge A → ℚ) :
    ∑ u, g u * diamondBoundary hN hM A f u =
      ∑ e, diamondCoboundary hN hM A g e * f e := by
  change (∑ u, g u * ∑ e, diamondIncidence hN hM A u e * f e) = _
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro e _
  calc
    (∑ u, g u * (diamondIncidence hN hM A u e * f e)) =
        (∑ u, diamondIncidence hN hM A u e * g u) * f e := by
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl (fun _ _ => by ring)
    _ = diamondCoboundary hN hM A g e * f e := by
      simp only [diamondIncidence, sub_mul, Finset.sum_sub_distrib, ite_mul, one_mul,
        zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true, diamondCoboundary_apply]

theorem ribbon_corner_pairing (hN : Even N) (hM : Even M) (A : RCConfig N M)
    (g : FaceVertex N M true → ℚ) (f : RibbonBoundaryComponent hN hM A → ℚ) :
    (∑ e : OpenDiamondEdge A,
      diamondCoboundary hN hM A g e * ribbonFaceBoundary hN hM A f e) =
      ∑ d : DirectedDart (checkerArrows N M),
        (g (ribbonFace hN hM d) -
          g (ribbonFace hN hM (ribbonEdgePairing hN hM A d))) *
          f (ribbonBoundaryOf hN hM A d) := by
  classical
  change (∑ e : OpenDiamondEdge A,
    (g (faceEndpoint hN hM true e.val true) - g (faceEndpoint hN hM true e.val false)) *
      (f (ribbonBoundaryOf hN hM A (ribbonEndEquiv hN hM (e.val, true))) -
        f (ribbonBoundaryOf hN hM A (ribbonEndEquiv hN hM (e.val, false))))) = _
  rw [← Finset.sum_subtype (univ.filter fun v => A v = true)
    (by intro v; simp) (fun v =>
      (g (faceEndpoint hN hM true v true) - g (faceEndpoint hN hM true v false)) *
        (f (ribbonBoundaryOf hN hM A (ribbonEndEquiv hN hM (v, true))) -
          f (ribbonBoundaryOf hN hM A (ribbonEndEquiv hN hM (v, false))))),
    Finset.sum_filter, ← (ribbonEndEquiv hN hM).sum_comp]
  conv_rhs => rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro v _
  simp only [Fintype.sum_bool, ribbonEdgePairing_end, ribbonFace_end]
  cases A v <;> simp only [Bool.false_xor, Bool.true_xor, Bool.not_true,
    Bool.not_false, Bool.false_eq_true, ite_true, ite_false]
  all_goals ring

theorem sum_ribbon_corner_pairing_eq_zero (hN : Even N) (hM : Even M) (A : RCConfig N M)
    (g : FaceVertex N M true → ℚ) (f : RibbonBoundaryComponent hN hM A → ℚ) :
    (∑ d : DirectedDart (checkerArrows N M),
      (g (ribbonFace hN hM d) -
        g (ribbonFace hN hM (ribbonEdgePairing hN hM A d))) *
        f (ribbonBoundaryOf hN hM A d)) = 0 := by
  simp_rw [sub_mul]
  rw [Finset.sum_sub_distrib]
  apply sub_eq_zero.mpr
  refine Fintype.sum_equiv (ribbonBoundary hN hM A) _ _ ?_
  intro d
  rw [ribbonBoundaryOf_step]
  have hp : ribbonEdgePairing hN hM A (ribbonBoundary hN hM A d) = faceRotation hN hM d :=
    ribbonEdgePairing_involutive hN hM A (faceRotation hN hM d)
  rw [hp]
  have hr : ribbonFace hN hM (faceRotation hN hM d) = ribbonFace hN hM d :=
    Subtype.ext ((sameCycle_faceRotation hN hM _ _).mp Equiv.Perm.SameCycle.rfl.apply_left)
  rw [hr]

/-- A capped ribbon face boundary is a conserved chain on the actual open graph. -/
theorem ribbonFaceBoundary_mem_cycleSpace (hN : Even N) (hM : Even M) (A : RCConfig N M)
    (f : RibbonBoundaryComponent hN hM A → ℚ) :
    ribbonFaceBoundary hN hM A f ∈ diamondCycleSpace hN hM A := by
  classical
  change diamondBoundary hN hM A (ribbonFaceBoundary hN hM A f) = 0
  funext u
  simp only [Pi.zero_apply]
  have he := diamondBoundary_pairing hN hM A (fun v => if u = v then 1 else 0)
    (ribbonFaceBoundary hN hM A f)
  rw [ribbon_corner_pairing] at he
  have hz := sum_ribbon_corner_pairing_eq_zero hN hM A (fun v => if u = v then 1 else 0) f
  simpa only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true] using he.trans hz

end PottsDiscontinuity.Torus
