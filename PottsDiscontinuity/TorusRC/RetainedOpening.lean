module

public import PottsDiscontinuity.TorusRC.FiberFiniteEnergy

/-! # Opening retained edge sets on every exact torus fiber -/

@[expose] public section

namespace PottsDiscontinuity.TorusRC

open Torus

variable {N M : ℕ}

noncomputable local instance retainedOpeningEdgeFintype (hN : Even N) (hM : Even M) :
    Fintype (fullDiamondGraph hN hM).edgeSet := Fintype.ofFinite _
noncomputable local instance retainedOpeningEdgeDecidableEq (hN : Even N) (hM : Even M) :
    DecidableEq (fullDiamondGraph hN hM).edgeSet := Classical.decEq _
noncomputable local instance retainedOpeningRemainingFintype (hN : Even N) (hM : Even M)
    (R : FK.Configuration (fullDiamondGraph hN hM)) :
    Fintype (FK.RemainingConfiguration (fullDiamondGraph hN hM) R) := Fintype.ofFinite _
noncomputable local instance retainedOpeningDeletedEdgeFintype (hN : Even N) (hM : Even M)
    (R : FK.Configuration (fullDiamondGraph hN hM)) :
    Fintype (FK.edgeRestriction (fullDiamondGraph hN hM) R).edgeSet := Fintype.ofFinite _

noncomputable section

/-- Each exact exterior fiber gives a prescribed retained-edge opening event
the usual finite-energy lower bound, uniformly in the exterior state. -/
theorem torusRCFiber_allOpen_ge (hN : Even N) (hM : Even M)
    (hN4 : 4 ≤ N) (hM4 : 4 ≤ M) (q : Set.Ici (1 : ℝ))
    (R : FK.Configuration (fullDiamondGraph hN hM))
    (H : FK.RemovedConfiguration (fullDiamondGraph hN hM) R)
    (s : FK.Configuration (FK.edgeRestriction (fullDiamondGraph hN hM) R)) :
    fkOpenEnergy (torusRCBridgeParameters q) ^ s.card ≤
      torusRCFiberEventProbability (torusRCFiberLaw hN hM hN4 hM4 q R H)
        {A | (FK.edgeRestrictionConfigurationEquiv (fullDiamondGraph hN hM) R s).val ⊆ A.val} := by
  exact (fk_remaining_allOpen_eventProbability_ge (fullDiamondGraph hN hM)
    (torusRCBridgeParameters q) (FK.BoundaryCondition.free ∅) R s).trans
      (torusRCFiberEventProbability_ge_free hN hM hN4 hM4 q R H _
        (fun _ _ hAB hA => hA.trans hAB))

/-- By fiber FKG, opening a retained collar costs at most its finite-energy
factor even in conjunction with any increasing event on that same fiber. -/
theorem torusRCFiber_allOpen_inter_ge (hN : Even N) (hM : Even M)
    (hN4 : 4 ≤ N) (hM4 : 4 ≤ M) (q : Set.Ici (1 : ℝ))
    (R : FK.Configuration (fullDiamondGraph hN hM))
    (H : FK.RemovedConfiguration (fullDiamondGraph hN hM) R)
    (s : FK.Configuration (FK.edgeRestriction (fullDiamondGraph hN hM) R))
    (E : Set (FK.RemainingConfiguration (fullDiamondGraph hN hM) R))
    (hE : IsUpperSet E) :
    fkOpenEnergy (torusRCBridgeParameters q) ^ s.card *
      torusRCFiberEventProbability (torusRCFiberLaw hN hM hN4 hM4 q R H) E ≤
      torusRCFiberEventProbability (torusRCFiberLaw hN hM hN4 hM4 q R H)
        ({A | (FK.edgeRestrictionConfigurationEquiv (fullDiamondGraph hN hM) R s).val ⊆ A.val} ∩ E) := by
  exact (mul_le_mul_of_nonneg_right
    (torusRCFiber_allOpen_ge hN hM hN4 hM4 q R H s)
    (torusRCFiberEventProbability_nonneg _ E)).trans
      (torusRCFiberEventProbability_inter_ge_mul hN hM hN4 hM4 q R H _ E
        (fun _ _ hAB hA => hA.trans hAB) hE)

end

end PottsDiscontinuity.TorusRC
