module

public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import Mathlib.Topology.Homotopy.Lifting
public import Mathlib.Topology.Homotopy.Path
public import PottsDiscontinuity.RCMProof.Contracts
public import PottsDiscontinuity.TorusExploration.Eq316

/-! Direct consumption check against the unchanged equation (3.16) contract
`RCMProof.contract_eq316` of the Theorem 1.2 assembly. -/

@[expose] public section

namespace PottsDiscontinuity.TorusExploration

/-- The exact contract `RCMProof.contract_eq316` is discharged by the proved equation (3.16). -/
theorem contract_eq316 : PottsDiscontinuity.RCMProof.contract_eq316 := eq316

end PottsDiscontinuity.TorusExploration
