module

public import PottsDiscontinuity.TorusExploration.ExteriorWinding
public import PottsDiscontinuity.TorusExploration.HorizontalPotential

/-! The full unexplored cylinder graph, including its currently closed edges. -/

@[expose] public section

namespace PottsDiscontinuity.TorusExploration
open Torus
variable {N M : ℕ}
noncomputable section
open scoped Classical

/-- All nonseam edges with both endpoints outside the explored cluster.
The original state of an edge between unexplored vertices is immaterial. -/
def unexploredCylinderConfig (hN : Even N) (hM : Even M) (A : RCConfig N M)
    (u : FaceVertex N M true) : RCConfig N M := fun e =>
  decide (e.2.val ≠ 0 ∧ ∀ b : Bool,
    (diamondOpenGraph hN hM true (TorusRC.torusRCSeamClosed A)).connectedComponentMk
      (faceEndpoint hN hM true e b) ≠
    (diamondOpenGraph hN hM true (TorusRC.torusRCSeamClosed A)).connectedComponentMk u)

/-- The full graph remaining after a crossing cluster is explored admits an
integer horizontal seam potential. -/
theorem unexploredCylinder_integerPotential (hN : Even N) (hM : Even M)
    (hNp : 0 < N) (hMlarge : 1 < M) {A : RCConfig N M}
    {u v : FaceVertex N M true} (hu : u.val.2.val=0) (hv : v.val.2.val+1=M)
    (hp : (diamondOpenGraph hN hM true (TorusRC.torusRCSeamClosed A)).Reachable u v) :
    ∃ F : FaceVertex N M true → ℤ,
      ∀ e : OpenDiamondEdge (unexploredCylinderConfig hN hM A u),
        F (faceEndpoint hN hM true e.val true) -
          F (faceEndpoint hN hM true e.val false) = integerSeamCrossX e.val := by
  apply exists_int_horizontalPotential
  intro g
  apply cylinderExterior_windingX_zero hN hM hNp hMlarge hu hv hp _ _ g
  intro e
  simpa only [unexploredCylinderConfig,decide_eq_true_eq] using e.property

end
end PottsDiscontinuity.TorusExploration
