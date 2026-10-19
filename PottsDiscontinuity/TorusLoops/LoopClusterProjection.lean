module

public import PottsDiscontinuity.Torus.DiamondIntersectionLocality
public import PottsDiscontinuity.TorusLoops.HorizontalHomology

/-!
# Projection of a medial boundary loop to its incident primal cluster

The lifted medial displacement equals the displacement of the open-ribbon
traversals, up to an explicit corner coboundary. This supplies a combinatorial
bridge from the fixed winding statistic to actual open clusters.
-/

@[expose] public section

open Finset PottsDiscontinuity.SixVertex

namespace PottsDiscontinuity.TorusLoops

open PottsDiscontinuity.Torus

variable {N M : ℕ}

/-- The actual primal cluster incident to a canonically oriented loop. -/
def loopPrimalCluster (hN : Even N) (hM : Even M) (A : RCConfig N M) :
    Loop hN hM (rcSmoothing A) →
      (diamondOpenGraph hN hM true A).ConnectedComponent :=
  Quotient.lift (fun d =>
    (diamondOpenGraph hN hM true A).connectedComponentMk (ribbonFace hN hM d))
    (fun _ _ h => SimpleGraph.ConnectedComponent.sound
      (ribbonConnected_reachable hN hM A
        (ribbonConnected_of_boundary_sameCycle hN hM A (by
          rwa [ribbonBoundary_eq_directedStep]))))

@[simp] theorem loopPrimalCluster_loopOf (hN : Even N) (hM : Even M)
    (A : RCConfig N M) (d : DirectedDart (checkerArrows N M)) :
    loopPrimalCluster hN hM A (directedLoopOf _ _
        (checkerArrows_compatible hN hM (rcSmoothing A)) d) =
      (diamondOpenGraph hN hM true A).connectedComponentMk (ribbonFace hN hM d) := rfl

/-- Horizontal offset of the incident primal face from a medial vertex. -/
def primalCornerOffsetX : Dart N M → ℤ
  | (_, .west) | (_, .north) => -1
  | _ => 0

/-- Vertical offset of the incident primal face from a medial vertex. -/
def primalCornerOffsetY : Dart N M → ℤ
  | (_, .west) | (_, .south) => -1
  | _ => 0

/-- Horizontal displacement of the ribbon traversal arriving at this end. -/
def arrivingRibbonX (A : RCConfig N M) (d : Dart N M) : ℤ :=
  if A d.1 then
    (if ribbonEndSide d.2 then 1 else -1) * (if checker d.1 then -1 else 1)
  else 0

/-- Vertical displacement of the ribbon traversal arriving at this end. -/
def arrivingRibbonY (A : RCConfig N M) (d : Dart N M) : ℤ :=
  if A d.1 then (if ribbonEndSide d.2 then -1 else 1) else 0

theorem horizontalIncrement_ribbon (hN : Even N) (hM : Even M)
    (A : RCConfig N M) (d : DirectedDart (checkerArrows N M)) :
    horizontalIncrement d.val =
      arrivingRibbonX A (stepPerm (rcSmoothing A) d.val) + primalCornerOffsetX d.val -
        primalCornerOffsetX (stepPerm (rcSmoothing A) d.val) := by
  rcases d with ⟨⟨⟨i, j⟩, p⟩, hd⟩
  rw [dartOut_checker_at hN hM] at hd
  have hx₁ := checker_prv_x hN i j
  have hx₂ := checker_nxt_x hN i j
  have hy₁ := checker_prv_y hM i j
  have hy₂ := checker_nxt_y hM i j
  cases ha : A (edgeReverse ((i, j), p)).1 <;> cases p <;>
    cases hc : checker (i, j) <;>
    simp_all [horizontalIncrement, arrivingRibbonX, primalCornerOffsetX,
      stepPerm_apply, strandReverse, rcSmoothing, edgeReverse,
      ribbonEndSide, pairedPort]

theorem verticalIncrement_ribbon (hN : Even N) (hM : Even M)
    (A : RCConfig N M) (d : DirectedDart (checkerArrows N M)) :
    verticalIncrement d.val =
      arrivingRibbonY A (stepPerm (rcSmoothing A) d.val) + primalCornerOffsetY d.val -
        primalCornerOffsetY (stepPerm (rcSmoothing A) d.val) := by
  rcases d with ⟨⟨⟨i, j⟩, p⟩, hd⟩
  rw [dartOut_checker_at hN hM] at hd
  have hx₁ := checker_prv_x hN i j
  have hx₂ := checker_nxt_x hN i j
  have hy₁ := checker_prv_y hM i j
  have hy₂ := checker_nxt_y hM i j
  cases ha : A (edgeReverse ((i, j), p)).1 <;> cases p <;>
    cases hc : checker (i, j) <;>
    simp_all [verticalIncrement, arrivingRibbonY, primalCornerOffsetY,
      stepPerm_apply, strandReverse, rcSmoothing, edgeReverse,
      ribbonEndSide, pairedPort]

private theorem loopSum_add (ω : ArrowConfig N M) (s : Smoothing N M)
    (h : CompatibleConfig ω s) (f g : Dart N M → ℤ) (q : DirectedLoop ω s h) :
    loopSum ω s h (fun d => f d + g d) q =
      loopSum ω s h f q + loopSum ω s h g q := by
  classical
  unfold loopSum
  rw [Finset.sum_add_distrib]

theorem loop_horizontal_arrivingRibbon (hN : Even N) (hM : Even M)
    (A : RCConfig N M) (q : Loop hN hM (rcSmoothing A)) :
    loopSum _ _ (checkerArrows_compatible hN hM (rcSmoothing A)) horizontalIncrement q =
      loopSum _ _ (checkerArrows_compatible hN hM (rcSmoothing A)) (arrivingRibbonX A) q := by
  have he : loopSum _ _ (checkerArrows_compatible hN hM (rcSmoothing A))
      horizontalIncrement q =
      loopSum _ _ (checkerArrows_compatible hN hM (rcSmoothing A))
        (fun d => arrivingRibbonX A (stepPerm (rcSmoothing A) d) +
          primalCornerOffsetX d - primalCornerOffsetX (stepPerm (rcSmoothing A) d)) q := by
    classical
    unfold loopSum
    exact Finset.sum_congr rfl (fun d _ => horizontalIncrement_ribbon hN hM A d)
  rw [he, loopSum_sub, loopSum_add, loopSum_step, loopSum_step]
  omega

theorem loop_vertical_arrivingRibbon (hN : Even N) (hM : Even M)
    (A : RCConfig N M) (q : Loop hN hM (rcSmoothing A)) :
    loopSum _ _ (checkerArrows_compatible hN hM (rcSmoothing A)) verticalIncrement q =
      loopSum _ _ (checkerArrows_compatible hN hM (rcSmoothing A)) (arrivingRibbonY A) q := by
  have he : loopSum _ _ (checkerArrows_compatible hN hM (rcSmoothing A))
      verticalIncrement q =
      loopSum _ _ (checkerArrows_compatible hN hM (rcSmoothing A))
        (fun d => arrivingRibbonY A (stepPerm (rcSmoothing A) d) +
          primalCornerOffsetY d - primalCornerOffsetY (stepPerm (rcSmoothing A) d)) q := by
    classical
    unfold loopSum
    exact Finset.sum_congr rfl (fun d _ => verticalIncrement_ribbon hN hM A d)
  rw [he, loopSum_sub, loopSum_add, loopSum_step, loopSum_step]
  omega

/-- Characteristic function of a specified medial loop on the ribbon boundaries. -/
noncomputable def loopBoundaryFunction (hN : Even N) (hM : Even M)
    (A : RCConfig N M) (q : Loop hN hM (rcSmoothing A)) :
    RibbonBoundaryComponent hN hM A → ℚ := by
  classical
  refine Quotient.lift (fun d => if directedLoopOf _ _
      (checkerArrows_compatible hN hM (rcSmoothing A)) d = q then 1 else 0) ?_
  intro d e h
  have he : directedLoopOf _ _ (checkerArrows_compatible hN hM (rcSmoothing A)) d =
      directedLoopOf _ _ (checkerArrows_compatible hN hM (rcSmoothing A)) e := by
    apply Quotient.sound
    rwa [ribbonBoundary_eq_directedStep] at h
  rw [he]

open scoped Classical in
@[simp] theorem loopBoundaryFunction_corner (hN : Even N) (hM : Even M)
    (A : RCConfig N M) (q : Loop hN hM (rcSmoothing A))
    (d : DirectedDart (checkerArrows N M)) :
    loopBoundaryFunction hN hM A q (ribbonBoundaryOf hN hM A d) =
      if directedLoopOf _ _ (checkerArrows_compatible hN hM (rcSmoothing A)) d = q
      then 1 else 0 := rfl

/-- A loop's boundary chain, supported on the actual open indexed edges. -/
noncomputable def loopBoundaryCycle (hN : Even N) (hM : Even M)
    (A : RCConfig N M) (q : Loop hN hM (rcSmoothing A)) :
    diamondCycleSpace hN hM A :=
  ⟨ribbonFaceBoundary hN hM A (loopBoundaryFunction hN hM A q),
    ribbonFaceBoundary_mem_cycleSpace hN hM A _⟩

@[simp] theorem arrivingRibbonX_end (A : RCConfig N M) (v : Fin N × Fin M) (b : Bool) :
    arrivingRibbonX A (ribbonEnd v b) =
      if A v then (if b then 1 else -1) * (if checker v then -1 else 1) else 0 := by
  cases hc : checker v <;> cases b <;> cases ha : A v <;>
    simp [arrivingRibbonX, ribbonEnd, ribbonEndSide, hc, ha]

@[simp] theorem arrivingRibbonY_end (A : RCConfig N M) (v : Fin N × Fin M) (b : Bool) :
    arrivingRibbonY A (ribbonEnd v b) = if A v then (if b then -1 else 1) else 0 := by
  cases hc : checker v <;> cases b <;> cases ha : A v <;>
    simp [arrivingRibbonY, ribbonEnd, ribbonEndSide, hc, ha]

private theorem sum_arrivingRibbonX (hN : Even N) (hM : Even M) (A : RCConfig N M)
    (f : DirectedDart (checkerArrows N M) → ℚ) :
    (∑ e : OpenDiamondEdge A, (if checker e.val then (-1 : ℚ) else 1) *
      (f (ribbonEndEquiv hN hM (e.val, true)) -
        f (ribbonEndEquiv hN hM (e.val, false)))) =
      ∑ d : DirectedDart (checkerArrows N M), f d * (arrivingRibbonX A d.val : ℚ) := by
  classical
  rw [← Finset.sum_subtype (univ.filter fun v => A v = true)
    (by intro v; simp) (fun v => (if checker v then (-1 : ℚ) else 1) *
      (f (ribbonEndEquiv hN hM (v, true)) - f (ribbonEndEquiv hN hM (v, false)))),
    Finset.sum_filter, ← (ribbonEndEquiv hN hM).sum_comp]
  conv_rhs => rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro v _
  cases ha : A v <;> cases hc : checker v <;>
    simp [arrivingRibbonX_end, ha, hc] <;> ring

private theorem sum_arrivingRibbonY (hN : Even N) (hM : Even M) (A : RCConfig N M)
    (f : DirectedDart (checkerArrows N M) → ℚ) :
    (∑ e : OpenDiamondEdge A, (-1 : ℚ) *
      (f (ribbonEndEquiv hN hM (e.val, true)) -
        f (ribbonEndEquiv hN hM (e.val, false)))) =
      ∑ d : DirectedDart (checkerArrows N M), f d * (arrivingRibbonY A d.val : ℚ) := by
  classical
  rw [← Finset.sum_subtype (univ.filter fun v => A v = true)
    (by intro v; simp) (fun v => (-1 : ℚ) *
      (f (ribbonEndEquiv hN hM (v, true)) - f (ribbonEndEquiv hN hM (v, false)))),
    Finset.sum_filter, ← (ribbonEndEquiv hN hM).sum_comp]
  conv_rhs => rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro v _
  cases ha : A v <;>
    simp [arrivingRibbonY_end, ha]; ring

private theorem sum_loopBoundaryFunction (hN : Even N) (hM : Even M)
    (A : RCConfig N M) (q : Loop hN hM (rcSmoothing A)) (g : Dart N M → ℤ) :
    (∑ d : DirectedDart (checkerArrows N M),
      loopBoundaryFunction hN hM A q (ribbonBoundaryOf hN hM A d) * (g d.val : ℚ)) =
      (loopSum _ _ (checkerArrows_compatible hN hM (rcSmoothing A)) g q : ℚ) := by
  classical
  unfold loopSum
  rw [Int.cast_sum, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro d _
  by_cases hd : directedLoopOf _ _ (checkerArrows_compatible hN hM (rcSmoothing A)) d = q
  · simp [hd]
  · simp [hd]

/-- The projected conserved primal chain carries exactly the horizontal medial displacement. -/
theorem loopBoundaryCycle_displacement_x (hN : Even N) (hM : Even M)
    (A : RCConfig N M) (q : Loop hN hM (rcSmoothing A)) :
    diamondHorizontalDisplacement A (loopBoundaryCycle hN hM A q).val =
      (loopSum _ _ (checkerArrows_compatible hN hM (rcSmoothing A)) horizontalIncrement q : ℚ) := by
  change (∑ e : OpenDiamondEdge A, (if checker e.val then (-1 : ℚ) else 1) *
    (loopBoundaryFunction hN hM A q (ribbonBoundaryOf hN hM A
        (ribbonEndEquiv hN hM (e.val, true))) -
      loopBoundaryFunction hN hM A q (ribbonBoundaryOf hN hM A
        (ribbonEndEquiv hN hM (e.val, false))))) = _
  rw [loop_horizontal_arrivingRibbon]
  exact (sum_arrivingRibbonX hN hM A
    (fun d => loopBoundaryFunction hN hM A q (ribbonBoundaryOf hN hM A d))).trans
      (sum_loopBoundaryFunction hN hM A q (arrivingRibbonX A))

/-- The projected conserved primal chain carries exactly the vertical medial displacement. -/
theorem loopBoundaryCycle_displacement_y (hN : Even N) (hM : Even M)
    (A : RCConfig N M) (q : Loop hN hM (rcSmoothing A)) :
    diamondVerticalDisplacement A (loopBoundaryCycle hN hM A q).val =
      (loopSum _ _ (checkerArrows_compatible hN hM (rcSmoothing A)) verticalIncrement q : ℚ) := by
  change -(∑ e : OpenDiamondEdge A,
    (loopBoundaryFunction hN hM A q (ribbonBoundaryOf hN hM A
        (ribbonEndEquiv hN hM (e.val, true))) -
      loopBoundaryFunction hN hM A q (ribbonBoundaryOf hN hM A
        (ribbonEndEquiv hN hM (e.val, false))))) = _
  rw [loop_vertical_arrivingRibbon]
  simpa only [neg_one_mul, Finset.sum_neg_distrib] using
    (sum_arrivingRibbonY hN hM A
      (fun d => loopBoundaryFunction hN hM A q (ribbonBoundaryOf hN hM A d))).trans
        (sum_loopBoundaryFunction hN hM A q (arrivingRibbonY A))

theorem loopPrimalCluster_end (hN : Even N) (hM : Even M) (A : RCConfig N M)
    (e : OpenDiamondEdge A) (b : Bool) :
    loopPrimalCluster hN hM A (directedLoopOf _ _
      (checkerArrows_compatible hN hM (rcSmoothing A))
      (ribbonEndEquiv hN hM (e.val, b))) = diamondEdgeCluster hN hM A e :=
  ribbonCornerCluster_end hN hM A e b

/-- A medial boundary loop projects entirely into its incident actual primal cluster. -/
theorem loopBoundaryCycle_supported (hN : Even N) (hM : Even M)
    (A : RCConfig N M) (q : Loop hN hM (rcSmoothing A)) :
    SupportedOnDiamondCluster hN hM A (loopPrimalCluster hN hM A q)
      (loopBoundaryCycle hN hM A q) := by
  classical
  intro e he
  have hn (b : Bool) : directedLoopOf _ _
      (checkerArrows_compatible hN hM (rcSmoothing A))
      (ribbonEndEquiv hN hM (e.val, b)) ≠ q := by
    intro hq
    apply he
    rw [← loopPrimalCluster_end hN hM A e b, hq]
  change loopBoundaryFunction hN hM A q
      (ribbonBoundaryOf hN hM A (ribbonEndEquiv hN hM (e.val, true))) -
    loopBoundaryFunction hN hM A q
      (ribbonBoundaryOf hN hM A (ribbonEndEquiv hN hM (e.val, false))) = 0
  simp [hn]

end PottsDiscontinuity.TorusLoops
