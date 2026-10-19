/- Adapted from an earlier, unpublished formalization of the planar FK model by the same author.
Probability statements use independent p and its true dual parameter. -/
module

public import PottsDiscontinuity.Duality.FiniteDuality
public import PottsDiscontinuity.Duality.RectangleDualCrossing
public import PottsDiscontinuity.Duality.RectangleCrossingExclusion

@[expose] public section

namespace PottsDiscontinuity.FK

open MeasureTheory PottsDiscontinuity.Duality
noncomputable section
attribute [local instance] configurationMeasurableSpace

def rectangleDualBottomTopCrossingEvent (a : LatticeVertex) (w h : ℕ) :
    Set (Configuration (rectangleDualGraph a w h)) :=
  {A | ∃ b ∈ rectangleDualBottomPorts a w h,
    ∃ t ∈ rectangleDualTopPorts a w h,
      ActualConnected (rectangleDualGraph a w h) A b t}

theorem rectangleHorizontalNoncrossing_subset_dualBottomTopCrossing_preimage
    (a : LatticeVertex) (w h : ℕ) :
    (rectangleHorizontalCrossingEvent a w h)ᶜ ⊆
      (rectanglePrimalDualConfigurationEquiv a w h) ⁻¹'
        rectangleDualBottomTopCrossingEvent a w h := by
  intro A hA
  change A ∉ rectangleHorizontalCrossingEvent a w h at hA
  have hdual := rectangleDualBottomTop_of_no_primal_horizontal_crossing a w h A hA
  change ∃ b ∈ rectangleDualBottomPorts a w h,
    ∃ t ∈ rectangleDualTopPorts a w h,
      ActualConnected (rectangleDualGraph a w h)
        (rectanglePrimalDualConfigurationEquiv a w h A) b t
  have heq : rectanglePrimalDualConfigurationEquiv a w h A =
      rectangleDualConfiguration a w h A := by
    rw [rectanglePrimalDualConfigurationEquiv_apply]
    rfl
  rw [heq]
  exact hdual

/-- The true dual bottom/top port event is exactly the complement of the
actual primal horizontal crossing event under the finite primal-dual map. -/
theorem rectangleHorizontalComplement_eq_dualBottomTop_preimage
    (a : LatticeVertex) (w h : ℕ) :
    (rectangleHorizontalCrossingEvent a w h)ᶜ =
      (rectanglePrimalDualConfigurationEquiv a w h) ⁻¹'
        rectangleDualBottomTopCrossingEvent a w h := by
  apply Set.ext
  intro A
  constructor
  · intro hA
    exact rectangleHorizontalNoncrossing_subset_dualBottomTopCrossing_preimage a w h hA
  · intro hdual
    change rectanglePrimalDualConfigurationEquiv a w h A ∈
      rectangleDualBottomTopCrossingEvent a w h at hdual
    rcases hdual with ⟨b, hb, t, ht, hconn⟩
    have hbrow : b.1.2 = a.2 - 1 := by
      rcases Finset.mem_image.mp hb with ⟨i, hi, rfl⟩
      rfl
    have htrow : t.1.2 = a.2 + (h : ℤ) := by
      rcases Finset.mem_image.mp ht with ⟨i, hi, rfl⟩
      rfl
    have hconfig : rectanglePrimalDualConfigurationEquiv a w h A =
        rectangleDualConfiguration a w h A := by
      rw [rectanglePrimalDualConfigurationEquiv_apply]
      rfl
    rw [hconfig] at hconn
    have hrow : A ∈ rectangleComplementDualVerticalCrossingEvent a w h :=
      ⟨b, t, hbrow, htrow, hconn⟩
    change A ∉ rectangleHorizontalCrossingEvent a w h
    intro hprimal
    exact rectanglePrimalDualCrossings_exclusive a w h A hprimal hrow

/-- Exactly one of the actual primal and complementary-dual crossings occurs. -/
theorem rectangle_crossing_duality (a : LatticeVertex) (w h : ℕ)
    (A : Configuration (rectangleGraph a w h)) :
    A ∉ rectangleHorizontalCrossingEvent a w h ↔
      rectanglePrimalDualConfigurationEquiv a w h A ∈
        rectangleDualBottomTopCrossingEvent a w h := by
  change A ∈ (rectangleHorizontalCrossingEvent a w h)ᶜ ↔ _
  rw [rectangleHorizontalComplement_eq_dualBottomTop_preimage]
  rfl

end
end PottsDiscontinuity.FK
