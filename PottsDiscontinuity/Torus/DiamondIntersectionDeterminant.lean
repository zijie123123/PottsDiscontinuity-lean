module

public import PottsDiscontinuity.Torus.DiamondHomologyCoordinates

/-!
# Intersection is the determinant of lifted displacement

Zero displacement is exactly a full-torus cellular boundary. Subtracting the two
explicit displacement classes therefore reduces any cycle to a boundary, giving
the determinant formula for the alternating intersection pairing.
-/

@[expose] public section

namespace PottsDiscontinuity.Torus

variable {N M : ℕ}

theorem fullDiamondDisplacement_eq_zero_iff (hN : Even N) (hM : Even M)
    (hNp : 0 < N) (hMp : 0 < M) (f : diamondCycleSpace hN hM (openRCConfig N M)) :
    fullDiamondDisplacementMap hN hM f = 0 ↔ f ∈ ribbonBoundarySpace hN hM (openRCConfig N M) := by
  constructor
  · intro hf
    have he : (ribbonBoundarySpace hN hM (openRCConfig N M)).mkQ f = 0 :=
      fullHomologyDisplacementMap_injective hN hM hNp hMp (by
        rw [fullHomologyDisplacementMap_mk, hf, map_zero])
    have hm : f ∈ LinearMap.ker (ribbonBoundarySpace hN hM (openRCConfig N M)).mkQ := he
    simpa only [Submodule.ker_mkQ] using hm
  · intro hf
    exact ribbonBoundarySpace_le_ker_displacement hN hM hf

/-- The full-torus cyclic-order form is the displacement determinant divided by NM. -/
theorem ribbonIntersection_mul_area (hN : Even N) (hM : Even M) (hNp : 0 < N) (hMp : 0 < M)
    (f g : diamondCycleSpace hN hM (openRCConfig N M)) :
    (N * M : ℚ) * ribbonIntersection hN hM (openRCConfig N M) f g =
      diamondHorizontalDisplacement (openRCConfig N M) f.val *
        diamondVerticalDisplacement (openRCConfig N M) g.val -
      diamondVerticalDisplacement (openRCConfig N M) f.val *
        diamondHorizontalDisplacement (openRCConfig N M) g.val := by
  let X := diamondHorizontalDisplacement (openRCConfig N M) f.val
  let Y := diamondVerticalDisplacement (openRCConfig N M) f.val
  let L : ℚ := N * M
  have hn : L ≠ 0 := by dsimp [L]; positivity
  let r := f + (Y / L) • verticalDiamondCycle hN hM + (X / L) • horizontalDiamondCycle hN hM
  have hr : fullDiamondDisplacementMap hN hM r = 0 := by
    dsimp only [r]
    rw [map_add, map_add, map_smul, map_smul, fullDiamondDisplacementMap_apply,
      fullDiamondDisplacementMap_vertical, fullDiamondDisplacementMap_horizontal]
    apply Prod.ext <;> simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst,
      Prod.smul_snd, smul_eq_mul, mul_zero, add_zero, Prod.fst_zero, Prod.snd_zero]
    all_goals dsimp [X, Y, L]; field_simp; ring
  have hb := (fullDiamondDisplacement_eq_zero_iff hN hM hNp hMp r).mp hr
  have he := ribbonIntersection_zero_of_mem_boundary hN hM (openRCConfig N M) r g hb
  dsimp only [r] at he
  rw [ribbonIntersection_add_left, ribbonIntersection_add_left,
    ribbonIntersection_smul_left, ribbonIntersection_smul_left,
    ribbonIntersection_vertical_eq_displacement, ribbonIntersection_horizontal_eq_displacement] at he
  have hm := congrArg (fun z : ℚ => L * z) he
  have hx : L * (Y / L * diamondHorizontalDisplacement (openRCConfig N M) g.val) =
      Y * diamondHorizontalDisplacement (openRCConfig N M) g.val := by field_simp
  have hy : L * (X / L * -diamondVerticalDisplacement (openRCConfig N M) g.val) =
      -(X * diamondVerticalDisplacement (openRCConfig N M) g.val) := by field_simp
  rw [mul_add, mul_add, hx, hy, mul_zero] at hm
  dsimp only [X, Y, L] at hm
  linarith

end PottsDiscontinuity.Torus
