/- Adapted from an earlier, unpublished formalization of the planar FK model by the same author.
Namespaces/imports adapted to the shared FK library. -/
module

public import PottsDiscontinuity.Duality.Rectangle
public import PottsDiscontinuity.FK.Graph
public import PottsDiscontinuity.FK.Model

@[expose] public section

namespace PottsDiscontinuity.FK

noncomputable section

variable (a : LatticeVertex) (w h : ℕ)

/-- Actual left-to-right open crossing of the full induced lattice rectangle.
The side endpoints are included as vertices; connectivity uses open graph
edges only and never boundary identifications. -/
def rectangleHorizontalCrossingEvent : Set (Configuration (rectangleGraph a w h)) :=
  {A | ∃ u v : RectangleVertex a w h,
    u.val ∈ rectangleLeftSide a w h ∧ v.val ∈ rectangleRightSide a w h ∧
      ActualConnected (rectangleGraph a w h) A u v}

attribute [local instance] configurationMeasurableSpace

end
end PottsDiscontinuity.FK
