module

public import PottsDiscontinuity.SixVertex.InfinityWeightComparison

/-! # The finite sine-product eigenvector equation -/

@[expose] public section

open Finset Matrix

namespace PottsDiscontinuity.SixVertex

variable {N n : ℕ}

/-- Changing the convention for a step does not change the full step sum. -/
theorem sum_sineLiftWeight_leftStepLift (r : ℕ) (L : ℝ) (x : Fin (2 * r) → ℤ) :
    (∑ d : Fin (2 * r) → Bool, sineLiftWeight L (leftStepLift x d)) =
      centeredCosineProduct r L * sineLiftWeight L x := by
  classical
  let e := Equiv.arrowCongr (Equiv.refl (Fin (2 * r))) Equiv.boolNot
  have he : ∀ d, leftStepLift x d = stepLift x (e d) := by
    intro d
    funext a
    change x a + (if d a then -1 else 1) = x a + (if !(d a) then 1 else -1)
    cases d a <;> rfl
  simp_rw [he]
  rw [e.sum_comp (fun d => sineLiftWeight L (stepLift x d))]
  exact sum_sineLiftWeight_stepLift r L x

private theorem sum_sineLiftWeight_leftStepLift_card {k : ℕ} (r : ℕ) (hk : k = 2 * r)
    (L : ℝ) (x : Fin k → ℤ) :
    (∑ d : Fin k → Bool, sineLiftWeight L (leftStepLift x d)) =
      centeredCosineProduct r L * sineLiftWeight L x := by
  subst k
  exact sum_sineLiftWeight_leftStepLift r L x

/-- The actual matrix row sum equals the unrestricted lifted walk sum: forbidden
choices contribute zero, including collisions across the cyclic seam. -/
theorem infinityRestriction_ground_row (hn : 0 < n) (hN : 2 ≤ N)
    (x : IndependentState N n) :
    (infinityRestriction N n *ᵥ (fun y => defectGroundWeight y.1.1)) x =
      ∑ d : Fin (defects x.1.1).card → Bool,
        sineLiftWeight ((N : ℝ) + (defects x.1.1).card)
          (leftStepLift (orderedDefectLift x.1.1) d) := by
  classical
  let e : (Fin (defects x.1.1).card → Bool) ≃ DefectChoice x.1.1 :=
    Equiv.arrowCongr ((defects x.1.1).orderIsoOfFin rfl).toEquiv (Equiv.refl Bool)
  let a := e.subtypeEquivOfSubtype (p := AdmissibleDefectChoice x.1.1)
  rw [infinityRestriction_mulVec_eq_sum_choices hn]
  rw [← a.sum_comp]
  change (∑ d : {d : Fin (defects x.1.1).card → Bool //
      AdmissibleDefectChoice x.1.1 (indexedDefectChoice x.1.1 d)},
    defectGroundWeight (upperOfHorizontal
      (horizontalOfDefectChoice x.1.1 (indexedDefectChoice x.1.1 d.1)))) = _
  trans ∑ d : {d : Fin (defects x.1.1).card → Bool //
      AdmissibleDefectChoice x.1.1 (indexedDefectChoice x.1.1 d)},
    sineLiftWeight ((N : ℝ) + (defects x.1.1).card)
      (leftStepLift (orderedDefectLift x.1.1) d.1)
  · apply sum_congr rfl
    intro d _
    exact defectGroundWeight_upper_eq_lift (by omega) x.2 d.1 d.2
  have hz : (∑ d : {d : Fin (defects x.1.1).card → Bool //
      ¬ AdmissibleDefectChoice x.1.1 (indexedDefectChoice x.1.1 d)},
      sineLiftWeight ((N : ℝ) + (defects x.1.1).card)
        (leftStepLift (orderedDefectLift x.1.1) d.1)) = 0 := by
    apply sum_eq_zero
    intro d _
    exact sineLiftWeight_inadmissible hN _ d.1 d.2
  have hs := Fintype.sum_subtype_add_sum_subtype
    (fun d => AdmissibleDefectChoice x.1.1 (indexedDefectChoice x.1.1 d))
    (fun d => sineLiftWeight ((N : ℝ) + (defects x.1.1).card)
      (leftStepLift (orderedDefectLift x.1.1) d))
  rw [hz, add_zero] at hs
  exact hs

/-- The positive defect sine product is an eigenvector of the genuine finite
limiting transfer matrix on independent states. -/
theorem infinityRestriction_defectGroundWeight_eigen (hn : 0 < n) {r : ℕ}
    (hN : N = 2 * (n + r)) :
    infinityRestriction N n *ᵥ (fun x => defectGroundWeight x.1.1) =
      centeredCosineProduct r ((N : ℝ) + 2 * r) • (fun x => defectGroundWeight x.1.1) := by
  classical
  funext x
  have hc := card_defects_eq_two_mul x.1 x.2 hN
  rw [infinityRestriction_ground_row hn (by omega)]
  rw [sum_sineLiftWeight_leftStepLift_card r hc, ← defectGroundWeight_eq_lift]
  simp only [hc, Nat.cast_mul, Nat.cast_ofNat, Pi.smul_apply, smul_eq_mul]

end PottsDiscontinuity.SixVertex
