module

public import PottsDiscontinuity.TorusRC.CylinderEvents

/-! Crossing the seam-closed cylinder from nonzero conserved vertical winding.
A component potential proves the geometric implication while retaining the
actual seam-closed cylinder of `TorusRC/CylinderEvents.lean` and its bottom/top rows. -/

@[expose] public section

open Finset PottsDiscontinuity.SixVertex
namespace PottsDiscontinuity.TorusTopology
open Torus TorusRC
variable {N M : ℕ}
noncomputable section

/-- A vertex reaches the top boundary in the actual seam-closed cylinder. -/
def cylinderReachesTop (hN : Even N) (hM : Even M) (A : RCConfig N M)
    (u : FaceVertex N M true) : Prop :=
  ∃ v, v.val.2.val+1=M ∧ (diamondOpenGraph hN hM true (torusRCSeamClosed A)).Reachable u v

end
end PottsDiscontinuity.TorusTopology
