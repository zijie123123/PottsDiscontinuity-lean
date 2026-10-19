module

public import PottsDiscontinuity.Torus.DiamondDisplacement
public import PottsDiscontinuity.Torus.RibbonIntersectionBoundary
public import PottsDiscontinuity.Torus.RibbonIntersectionLinear

/-!
# Displacement coordinates of full torus homology

Intersection with the two explicit conserved flows gives the two lifted displacement
coordinates. They descend through actual cellular boundaries and identify the full
capped first homology with the rational coordinate plane.
-/

@[expose] public section

namespace PottsDiscontinuity.Torus

open Module

variable {N M : ℕ}

/-- The full-torus displacement map, expressed by its two intersection coordinates. -/
def fullDiamondDisplacementMap (hN : Even N) (hM : Even M) :
    diamondCycleSpace hN hM (openRCConfig N M) →ₗ[ℚ] (ℚ × ℚ) where
  toFun f := (ribbonIntersection hN hM (openRCConfig N M) (verticalDiamondCycle hN hM) f,
    -ribbonIntersection hN hM (openRCConfig N M) (horizontalDiamondCycle hN hM) f)
  map_add' f g := by
    apply Prod.ext
    · exact ribbonIntersection_add_right hN hM _ _ f g
    · change -ribbonIntersection hN hM _ _ (f + g) =
        -ribbonIntersection hN hM _ _ f + -ribbonIntersection hN hM _ _ g
      rw [ribbonIntersection_add_right]
      ring
  map_smul' c f := by
    apply Prod.ext
    · exact ribbonIntersection_smul_right hN hM _ _ f c
    · change -ribbonIntersection hN hM _ _ (c • f) = c * -ribbonIntersection hN hM _ _ f
      rw [ribbonIntersection_smul_right]
      ring

theorem fullDiamondDisplacementMap_apply (hN : Even N) (hM : Even M)
    (f : diamondCycleSpace hN hM (openRCConfig N M)) :
    fullDiamondDisplacementMap hN hM f =
      (diamondHorizontalDisplacement (openRCConfig N M) f.val,
        diamondVerticalDisplacement (openRCConfig N M) f.val) := by
  apply Prod.ext
  · exact ribbonIntersection_vertical_eq_displacement hN hM f
  · change -ribbonIntersection hN hM _ _ f = _
    rw [ribbonIntersection_horizontal_eq_displacement, neg_neg]

theorem fullDiamondDisplacementMap_vertical (hN : Even N) (hM : Even M) :
    fullDiamondDisplacementMap hN hM (verticalDiamondCycle hN hM) = (0, -(N * M : ℚ)) := by
  rw [fullDiamondDisplacementMap_apply, verticalDiamondCycle_displacement_x,
    verticalDiamondCycle_displacement_y]

theorem fullDiamondDisplacementMap_horizontal (hN : Even N) (hM : Even M) :
    fullDiamondDisplacementMap hN hM (horizontalDiamondCycle hN hM) = (-(N * M : ℚ), 0) := by
  rw [fullDiamondDisplacementMap_apply, horizontalDiamondCycle_displacement_x,
    horizontalDiamondCycle_displacement_y]

theorem ribbonBoundarySpace_le_ker_displacement (hN : Even N) (hM : Even M) :
    ribbonBoundarySpace hN hM (openRCConfig N M) ≤ LinearMap.ker (fullDiamondDisplacementMap hN hM) := by
  intro f hf
  change fullDiamondDisplacementMap hN hM f = 0
  apply Prod.ext
  · change ribbonIntersection hN hM _ _ f = 0
    rw [ribbonIntersection_antisymm,
      ribbonIntersection_zero_of_mem_boundary hN hM _ f _ hf, neg_zero]
  · change -ribbonIntersection hN hM _ _ f = 0
    rw [ribbonIntersection_antisymm,
      ribbonIntersection_zero_of_mem_boundary hN hM _ f _ hf, neg_zero, neg_zero]

/-- Actual displacement descends through the full torus cellular boundary subspace. -/
def fullHomologyDisplacementMap (hN : Even N) (hM : Even M) :
    CappedRibbonHomology hN hM (openRCConfig N M) →ₗ[ℚ] (ℚ × ℚ) :=
  (ribbonBoundarySpace hN hM (openRCConfig N M)).liftQ (fullDiamondDisplacementMap hN hM)
    (ribbonBoundarySpace_le_ker_displacement hN hM)

@[simp] theorem fullHomologyDisplacementMap_mk (hN : Even N) (hM : Even M)
    (f : diamondCycleSpace hN hM (openRCConfig N M)) :
    fullHomologyDisplacementMap hN hM ((ribbonBoundarySpace hN hM (openRCConfig N M)).mkQ f) =
      fullDiamondDisplacementMap hN hM f := rfl

theorem fullHomologyDisplacementMap_surjective (hN : Even N) (hM : Even M)
    (hNp : 0 < N) (hMp : 0 < M) : Function.Surjective (fullHomologyDisplacementMap hN hM) := by
  have hn : (N * M : ℚ) ≠ 0 := by positivity
  rintro ⟨x, y⟩
  refine ⟨(ribbonBoundarySpace hN hM (openRCConfig N M)).mkQ
    ((-y / (N * M : ℚ)) • verticalDiamondCycle hN hM +
      (-x / (N * M : ℚ)) • horizontalDiamondCycle hN hM), ?_⟩
  rw [fullHomologyDisplacementMap_mk, map_add, map_smul, map_smul,
    fullDiamondDisplacementMap_vertical, fullDiamondDisplacementMap_horizontal]
  apply Prod.ext <;> simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst,
    Prod.smul_snd, smul_eq_mul, mul_zero, zero_add, add_zero] <;> field_simp

theorem fullHomologyDisplacementMap_injective (hN : Even N) (hM : Even M)
    (hNp : 0 < N) (hMp : 0 < M) : Function.Injective (fullHomologyDisplacementMap hN hM) := by
  have hd : finrank ℚ (CappedRibbonHomology hN hM (openRCConfig N M)) = finrank ℚ (ℚ × ℚ) := by
    rw [finrank_cappedRibbonHomology_open hN hM hNp hMp, Module.finrank_prod, finrank_self]
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hd).mpr
    (fullHomologyDisplacementMap_surjective hN hM hNp hMp)

end PottsDiscontinuity.Torus
