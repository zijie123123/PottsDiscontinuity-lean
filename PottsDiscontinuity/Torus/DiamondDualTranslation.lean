module

public import PottsDiscontinuity.Torus.DiamondGraph

/-!
# Translating the dual diamond graph to the primal colour

A horizontal unit translation exchanges the face colours and carries every indexed
diamond edge to the corresponding edge. This lets the already proved primal ribbon
theory apply to the actual complementary dual configuration.
-/

@[expose] public section

open PottsDiscontinuity.SixVertex

namespace PottsDiscontinuity.Torus

variable {N M : ℕ}

/-- Translate an indexed configuration one unit horizontally. -/
def shiftRCConfig (A : RCConfig N M) : RCConfig N M := fun v => A (prv v.1, v.2)

@[simp] theorem shiftRCConfig_nxt (A : RCConfig N M) (v : Fin N × Fin M) :
    shiftRCConfig A (nxt v.1, v.2) = A v := by
  simp only [shiftRCConfig, nxt, prv, Equiv.symm_apply_apply]

/-- The complementary dual configuration, represented on the primal-colour carrier. -/
def translatedDualConfig (A : RCConfig N M) : RCConfig N M := shiftRCConfig (dualConfig A)

end PottsDiscontinuity.Torus
