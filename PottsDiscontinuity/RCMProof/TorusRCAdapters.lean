module

public import PottsDiscontinuity.RCMProof.Contracts
public import PottsDiscontinuity.TorusRC.Eq315

@[expose] public section

namespace PottsDiscontinuity.RCMProof

/-- The exact (3.15) contract is the proved TorusRC theorem, with its honest
equation (3.19) premise retained. -/
theorem contract_eq315_proved : contract_eq315 := by
  intro q hh319
  exact TorusRC.eq315 q hh319

end PottsDiscontinuity.RCMProof
