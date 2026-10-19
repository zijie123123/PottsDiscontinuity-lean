module

public import PottsDiscontinuity.FK.DomainMarkov
public import PottsDiscontinuity.TorusRC.MeasureBridge

/-! # Conditional finite-state laws on frozen torus edge fibers -/

@[expose] public section

namespace PottsDiscontinuity.TorusRC

open Torus

variable {N M : ℕ}

noncomputable local instance torusFiberGraphFintype (hN : Even N) (hM : Even M) :
    Fintype (fullDiamondGraph hN hM).edgeSet := Fintype.ofFinite _

noncomputable local instance torusFiberGraphDecidableEq (hN : Even N) (hM : Even M) :
    DecidableEq (fullDiamondGraph hN hM).edgeSet := Classical.decEq _

noncomputable local instance torusFiberRemainingFintype (hN : Even N) (hM : Even M)
    (R : FK.Configuration (fullDiamondGraph hN hM)) :
    Fintype (FK.RemainingConfiguration (fullDiamondGraph hN hM) R) := Fintype.ofFinite _

noncomputable section

/-- The torus conditional law on the remaining edges when an exact state of
the removed edge set is fixed. We define it by normalizing the torus masses on
that fiber. -/
def torusRCFiberLaw (hN : Even N) (hM : Even M) (hN4 : 4 ≤ N) (hM4 : 4 ≤ M)
    (q : Set.Ici (1 : ℝ)) (R : FK.Configuration (fullDiamondGraph hN hM))
    (H : FK.RemovedConfiguration (fullDiamondGraph hN hM) R) :
    PMF (FK.RemainingConfiguration (fullDiamondGraph hN hM) R) := by
  classical
  exact FK.FiniteProbability.pmf
    (fun A => torusRCMass hN hM q
      ((torusRCConfigurationEquiv hN hM hN4 hM4).symm (A.val ∪ H.val)))
    (fun A => torusRCMass_pos hN hM q
      ((torusRCConfigurationEquiv hN hM hN4 hM4).symm (A.val ∪ H.val)))

private theorem torusRCFiberMass_eq_fk (hN : Even N) (hM : Even M)
    (hN4 : 4 ≤ N) (hM4 : 4 ≤ M) (q : Set.Ici (1 : ℝ))
    (R : FK.Configuration (fullDiamondGraph hN hM))
    (H : FK.RemovedConfiguration (fullDiamondGraph hN hM) R)
    (A : FK.RemainingConfiguration (fullDiamondGraph hN hM) R) :
    torusRCMass hN hM q
        ((torusRCConfigurationEquiv hN hM hN4 hM4).symm (A.val ∪ H.val)) =
      FK.configurationProbability (fullDiamondGraph hN hM)
        (torusRCBridgeParameters q) (FK.BoundaryCondition.free ∅)
        (A.val ∪ H.val) := by
  rw [torusRCMass_eq_fk_configurationProbability hN hM hN4 hM4 q]
  simp

/-- Conditioning the torus law on a complete exterior state gives exactly the
FK frozen-fiber law, hence the existing domain-Markov remaining-edge law with
the boundary partition induced by the frozen open edges. -/
theorem torusRCFiberLaw_eq_remainingLaw (hN : Even N) (hM : Even M)
    (hN4 : 4 ≤ N) (hM4 : 4 ≤ M) (q : Set.Ici (1 : ℝ))
    (R : FK.Configuration (fullDiamondGraph hN hM))
    (H : FK.RemovedConfiguration (fullDiamondGraph hN hM) R) :
    torusRCFiberLaw hN hM hN4 hM4 q R H =
      FK.remainingLaw (fullDiamondGraph hN hM) (torusRCBridgeParameters q)
        (FK.frozenBoundary (FK.BoundaryCondition.free ∅) H.val) R := by
  classical
  have hmass (A : FK.RemainingConfiguration (fullDiamondGraph hN hM) R) :=
    torusRCFiberMass_eq_fk hN hM hN4 hM4 q R H A
  have hden :
      (∑ A : FK.RemainingConfiguration (fullDiamondGraph hN hM) R,
        torusRCMass hN hM q
          ((torusRCConfigurationEquiv hN hM hN4 hM4).symm (A.val ∪ H.val))) =
      ∑ A : FK.RemainingConfiguration (fullDiamondGraph hN hM) R,
        FK.configurationProbability (fullDiamondGraph hN hM)
          (torusRCBridgeParameters q) (FK.BoundaryCondition.free ∅)
          (A.val ∪ H.val) := by
    apply Finset.sum_congr rfl
    intro A _
    exact hmass A
  have hfiber : torusRCFiberLaw hN hM hN4 hM4 q R H =
      FK.frozenFiberLaw (torusRCBridgeParameters q)
        (FK.BoundaryCondition.free ∅) R H := by
    ext A
    simp only [torusRCFiberLaw, FK.frozenFiberLaw,
      FK.FiniteProbability.pmf_apply, FK.FiniteProbability.partition]
    rw [hmass A, hden]
  rw [hfiber]
  exact FK.frozenFiberLaw_eq_remainingLaw
    (torusRCBridgeParameters q) (FK.BoundaryCondition.free ∅) R H

end

end PottsDiscontinuity.TorusRC
