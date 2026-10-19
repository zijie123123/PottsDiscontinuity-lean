module

public import PottsDiscontinuity.Torus.LoopReorientation
public import PottsDiscontinuity.Torus.LoopStatistics

/-!
# Vertical winding is independent of loop orientation

The explicit loop equivalence and edge-antisymmetry of algebraic crossings show
that reversing loops preserves their absolute vertical winding. This identifies the
canonical RC statistic U with the winding count in every compatible arrow orientation,
and proves the sector inclusion needed for Corollary 3.13(iii).
-/

@[expose] public section

open Finset PottsDiscontinuity.SixVertex

namespace PottsDiscontinuity.Torus

variable {N M : ℕ}

/-- A loop's vertical winding is preserved or negated, according to its orientation. -/
theorem loopVertical_reorient (ω₀ ω₁ : ArrowConfig N M) (s : Smoothing N M)
    (h₀ : CompatibleConfig ω₀ s) (h₁ : CompatibleConfig ω₁ s) (j : Fin M)
    (q : DirectedLoop ω₀ s h₀) :
    loopVertical ω₁ s h₁ j (loopReorientEquiv ω₀ ω₁ s h₀ h₁ q) =
      if loopOrientation ω₀ s h₀ ω₁ h₁ q then loopVertical ω₀ s h₀ j q
      else -loopVertical ω₀ s h₀ j q :=
  loopSum_reorient ω₀ ω₁ s h₀ h₁ (verticalCross j) (verticalCross_edgeReverse j) q

/-- The sum of absolute windings is independent of all loop-reversal choices. -/
theorem verticalMass_reorient (ω₀ ω₁ : ArrowConfig N M) (s : Smoothing N M)
    (h₀ : CompatibleConfig ω₀ s) (h₁ : CompatibleConfig ω₁ s) (j : Fin M) :
    verticalMass ω₁ s h₁ j = verticalMass ω₀ s h₀ j := by
  classical
  unfold verticalMass
  rw [← (loopReorientEquiv ω₀ ω₁ s h₀ h₁).sum_comp]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [loopVertical_reorient]
  by_cases hq : loopOrientation ω₀ s h₀ ω₁ h₁ q = true
  · simp only [hq, ite_true]
  · simp only [Bool.eq_false_iff.mpr hq, Bool.false_eq_true, ite_false, Int.natAbs_neg]

theorem verticalWindingCount_reorient (ω₀ ω₁ : ArrowConfig N M) (s : Smoothing N M)
    (h₀ : CompatibleConfig ω₀ s) (h₁ : CompatibleConfig ω₁ s) (j : Fin M) :
    verticalWindingCount ω₁ s h₁ j = verticalWindingCount ω₀ s h₀ j := by
  unfold verticalWindingCount
  rw [verticalMass_reorient ω₀ ω₁ s h₀ h₁ j]

/-- The canonically defined RC statistic equals the winding count of any of its orientations. -/
theorem rcVerticalWinding_eq_oriented (hN : Even N) (hM : Even M) (j : Fin M)
    (A : RCConfig N M) (ω : ArrowConfig N M) (h : CompatibleConfig ω (rcSmoothing A)) :
    rcVerticalWinding hN hM j A = verticalWindingCount ω (rcSmoothing A) h j :=
  (verticalWindingCount_reorient (checkerArrows N M) ω (rcSmoothing A)
    (checkerArrows_compatible hN hM (rcSmoothing A)) h j).symm

/-- The actual RC configuration underlying an oriented loop configuration in sector r
has U at least r. This is the event inclusion in the proof of Corollary 3.13(iii),
without assuming the unproved FK weight identity or a turning-number classification. -/
theorem sector_le_rcVerticalWinding (hN : Even N) (hM : Even M) (j : Fin M)
    (A : RCConfig N M) (ω : ArrowConfig N M) (h : CompatibleConfig ω (rcSmoothing A))
    {r : ℕ} (hr : ω.absUp + r = N / 2) : r ≤ rcVerticalWinding hN hM j A := by
  rw [rcVerticalWinding_eq_oriented hN hM j A ω h]
  exact sector_le_verticalWindingCount hN ω (rcSmoothing A) h j hr

end PottsDiscontinuity.Torus
