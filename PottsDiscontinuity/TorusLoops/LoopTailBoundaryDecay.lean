module

public import PottsDiscontinuity.TorusLoops.RectangleExplorationProductBound

/-!
# Boundary-decay input for the rotated-box one-arm probabilities

The exploration estimate loses one unit in the rotated square radius. This
module transfers the stated free-boundary connection decay to that sequence.
-/

@[expose] public section

open Filter Topology

namespace PottsDiscontinuity.TorusLoops

open PottsDiscontinuity.FK
open PottsDiscontinuity.Zhang

/-- The exact square-lattice form of the input
`φ⁰_L(0 ↔ ∂Λ_n) → 0`, expressed using the FK free-box limit and Zhang's
boundary-connection event. -/
theorem tendsto_rectangleFreeOneArmProbability_of_boundaryConnection_zero
    (q : Set.Ici (1 : ℝ))
    (hzero : Tendsto
      (fun n => (((Classical.choose (freeBoxLimit_existsUnique
        (rectangleFKParameters q))) (boundaryConnectionEvent n) : NNReal) : ℝ))
      atTop (𝓝 0)) :
    Tendsto (fun n => rectangleFreeOneArmProbability q (n / 2 - 1))
      atTop (𝓝 0) := by
  have hrad : Tendsto (fun n : ℕ => n / 2 - 1) atTop atTop := by
    apply tendsto_atTop.2
    intro k
    filter_upwards [eventually_ge_atTop (2 * (k + 1))] with n hn
    omega
  have hcomp := hzero.comp hrad
  refine hcomp.congr' ?_
  filter_upwards with n
  simp [Function.comp_apply, rectangleFreeOneArmProbability,
    boundaryConnectionEvent_eq_oneArmEvent]

end PottsDiscontinuity.TorusLoops
