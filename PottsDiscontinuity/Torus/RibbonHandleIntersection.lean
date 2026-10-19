module

public import PottsDiscontinuity.Torus.RibbonIntersectionBoundary

/-!
# Handles and nonzero cellular intersection

The capped homology dimension and the exact radical theorem characterize the
presence of a handle by two conserved flows with nonzero cyclic-order intersection.
The comparison of this criterion with the torus winding determinant is separate.
-/

@[expose] public section

namespace PottsDiscontinuity.Torus

open Module

variable {N M : ℕ}

theorem ribbonBoundarySpace_eq_top_iff (hN : Even N) (hM : Even M) (A : RCConfig N M) :
    ribbonBoundarySpace hN hM A = ⊤ ↔ ribbonHandleCount hN hM A = 0 := by
  have hq := (ribbonBoundarySpace hN hM A).finrank_quotient_add_finrank
  have he := finrank_cappedRibbonHomology hN hM A
  change finrank ℚ (CappedRibbonHomology hN hM A) +
    finrank ℚ (ribbonBoundarySpace hN hM A) = finrank ℚ (diamondCycleSpace hN hM A) at hq
  constructor
  · intro ht
    have hb : finrank ℚ (ribbonBoundarySpace hN hM A) = finrank ℚ (diamondCycleSpace hN hM A) := by
      rw [ht, finrank_top]
    omega
  · intro hz
    apply Submodule.eq_top_of_finrank_eq
    omega

theorem ribbonHandleCount_zero_iff_intersection_zero (hN : Even N) (hM : Even M)
    (A : RCConfig N M) :
    ribbonHandleCount hN hM A = 0 ↔
      ∀ f g : diamondCycleSpace hN hM A, ribbonIntersection hN hM A f g = 0 := by
  constructor
  · intro hz f g
    apply ribbonIntersection_zero_of_mem_boundary hN hM A f g
    rw [(ribbonBoundarySpace_eq_top_iff hN hM A).mpr hz]
    trivial
  · intro h
    apply (ribbonBoundarySpace_eq_top_iff hN hM A).mp
    apply top_unique
    intro f _
    exact mem_ribbonBoundarySpace_of_intersection_zero hN hM A f (h f)

/-- A handle exists exactly when two actual conserved flows have nonzero intersection. -/
theorem ribbonHandleCount_one_iff_intersection_nonzero (hN : Even N) (hM : Even M)
    (A : RCConfig N M) :
    ribbonHandleCount hN hM A = 1 ↔
      ∃ f g : diamondCycleSpace hN hM A, ribbonIntersection hN hM A f g ≠ 0 := by
  classical
  have hz := ribbonHandleCount_zero_iff_intersection_zero hN hM A
  have hb := ribbonHandleCount_le_one hN hM A
  constructor
  · intro ho
    by_contra hn
    push Not at hn
    have he := hz.mpr hn
    omega
  · rintro ⟨f, g, hfg⟩
    have hn : ribbonHandleCount hN hM A ≠ 0 := fun h => hfg (hz.mp h f g)
    omega

end PottsDiscontinuity.Torus
