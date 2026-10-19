module

public import PottsDiscontinuity.TorusRC.CylinderFiberComparison
public import PottsDiscontinuity.TorusRC.RectanglePairs

/-! # Joint disintegration retaining the exterior configuration -/

@[expose] public section

namespace PottsDiscontinuity.TorusRC

open Torus

variable {N M : ℕ}

noncomputable local instance splitGraphFintype (hN : Even N) (hM : Even M) :
    Fintype (fullDiamondGraph hN hM).edgeSet := Fintype.ofFinite _

noncomputable local instance splitGraphDecidableEq (hN : Even N) (hM : Even M) :
    DecidableEq (fullDiamondGraph hN hM).edgeSet := Classical.decEq _

noncomputable section

open scoped Classical in
private theorem map_pair_right_apply {α β : Type*} (p : PMF α) (b : β) (x : α × β) :
    p.map (fun a => (a, b)) x = if x.2 = b then p x.1 else 0 := by
  classical
  rcases x with ⟨x, y⟩
  by_cases hy : y = b
  · subst b
    simp only [PMF.map_apply, Prod.mk.injEq, and_true, ite_true, tsum_ite_eq']
  · simp only [PMF.map_apply, Prod.mk.injEq, hy, and_false, ite_false, tsum_zero]

/-- The torus law disintegrates jointly into the actual exterior marginal and
the exact conditional FK fiber law, retaining the exterior as a coordinate. -/
theorem torusRCPMF_map_split_eq_bind_fiber (hN : Even N) (hM : Even M)
    (hN4 : 4 ≤ N) (hM4 : 4 ≤ M) (q : Set.Ici (1 : ℝ))
    (R : FK.Configuration (fullDiamondGraph hN hM)) :
    (torusRCPMF hN hM q).map
        (fun A => FK.configurationSplitEquiv (fullDiamondGraph hN hM) R
          (torusRCConfigurationEquiv hN hM hN4 hM4 A)) =
      (FK.frozenMarginalLaw (torusRCBridgeParameters q)
        (FK.BoundaryCondition.free ∅) R).bind
        (fun H => (torusRCFiberLaw hN hM hN4 hM4 q R H).map
          (fun A => (A, H))) := by
  classical
  have hmap :
      (torusRCPMF hN hM q).map
          (fun A => FK.configurationSplitEquiv (fullDiamondGraph hN hM) R
            (torusRCConfigurationEquiv hN hM hN4 hM4 A)) =
        ((torusRCPMF hN hM q).map
          (torusRCConfigurationEquiv hN hM hN4 hM4)).map
          (FK.configurationSplitEquiv (fullDiamondGraph hN hM) R) := by
    exact (PMF.map_comp _ _ _).symm
  rw [hmap, torusRCPMF_map_edgeEquiv hN hM hN4 hM4 q]
  ext ⟨A, H⟩
  rw [FK.FiniteProbability.map_equiv_apply, FK.configurationSplitEquiv_symm_apply,
    FK.law_restore_eq_conditional_mul_marginal]
  rw [PMF.bind_apply]
  simp_rw [map_pair_right_apply]
  simp only [mul_ite, mul_zero, tsum_ite_eq']
  rw [torusRCFiberLaw_eq_remainingLaw hN hM hN4 hM4 q R H, mul_comm]

/-- Real event probabilities are expectations of their indicator functions. -/
theorem torusRCProbability_eq_expectation (hN : Even N) (hM : Even M)
    (q : Set.Ici (1 : ℝ)) (E : Set (RCConfig N M)) :
    torusRCProbability hN hM q E =
      FK.FiniteProbability.expectation (torusRCPMF hN hM q)
        (E.indicator (fun _ => (1 : ℝ))) := by
  classical
  rw [torusRCProbability_eq_sum, FK.FiniteProbability.expectation]
  apply Finset.sum_congr rfl
  intro A _
  by_cases hA : A ∈ E <;>
    simp [Set.indicator, hA, torusRCPMF_apply,
      ENNReal.toReal_ofReal (torusRCMass_pos hN hM q A).le]

local instance splitRemainingFintype (hN : Even N) (hM : Even M)
    (R : FK.Configuration (fullDiamondGraph hN hM)) :
    Fintype (FK.RemainingConfiguration (fullDiamondGraph hN hM) R) := Fintype.ofFinite _

local instance splitRemovedFintype (hN : Even N) (hM : Even M)
    (R : FK.Configuration (fullDiamondGraph hN hM)) :
    Fintype (FK.RemovedConfiguration (fullDiamondGraph hN hM) R) := Fintype.ofFinite _

/-- Exact expectation disintegration, with both the retained and frozen edge
states available to the observable. -/
theorem torusRCPMF_expectation_split (hN : Even N) (hM : Even M)
    (hN4 : 4 ≤ N) (hM4 : 4 ≤ M) (q : Set.Ici (1 : ℝ))
    (R : FK.Configuration (fullDiamondGraph hN hM))
    (f : FK.RemainingConfiguration (fullDiamondGraph hN hM) R ×
      FK.RemovedConfiguration (fullDiamondGraph hN hM) R → ℝ) :
    FK.FiniteProbability.expectation (torusRCPMF hN hM q)
        (fun A => f (FK.configurationSplitEquiv (fullDiamondGraph hN hM) R
          (torusRCConfigurationEquiv hN hM hN4 hM4 A))) =
      FK.FiniteProbability.expectation
        (FK.frozenMarginalLaw (torusRCBridgeParameters q) (FK.BoundaryCondition.free ∅) R)
        (fun H => FK.FiniteProbability.expectation
          (torusRCFiberLaw hN hM hN4 hM4 q R H) (fun A => f (A, H))) := by
  rw [← FK.FiniteProbability.expectation_map,
    torusRCPMF_map_split_eq_bind_fiber hN hM hN4 hM4 q R,
    FK.FiniteProbability.expectation_bind]
  simp_rw [FK.FiniteProbability.expectation_map]

/-- Joint event probabilities are averaged over exactly the exterior states
in the exterior event, using their actual marginal probabilities. -/
theorem torusRCProbability_split_event (hN : Even N) (hM : Even M)
    (hN4 : 4 ≤ N) (hM4 : 4 ≤ M) (q : Set.Ici (1 : ℝ))
    (R : FK.Configuration (fullDiamondGraph hN hM))
    (S : Set (FK.RemovedConfiguration (fullDiamondGraph hN hM) R))
    (E : FK.RemovedConfiguration (fullDiamondGraph hN hM) R →
      Set (FK.RemainingConfiguration (fullDiamondGraph hN hM) R)) :
    torusRCProbability hN hM q {A |
      let P := FK.configurationSplitEquiv (fullDiamondGraph hN hM) R
        (torusRCConfigurationEquiv hN hM hN4 hM4 A)
      P.2 ∈ S ∧ P.1 ∈ E P.2} =
    FK.FiniteProbability.expectation
      (FK.frozenMarginalLaw (torusRCBridgeParameters q) (FK.BoundaryCondition.free ∅) R)
      (S.indicator (fun H => torusRCFiberEventProbability
        (torusRCFiberLaw hN hM hN4 hM4 q R H) (E H))) := by
  classical
  let T : Set (FK.RemainingConfiguration (fullDiamondGraph hN hM) R ×
      FK.RemovedConfiguration (fullDiamondGraph hN hM) R) :=
    {P | P.2 ∈ S ∧ P.1 ∈ E P.2}
  rw [torusRCProbability_eq_expectation]
  change FK.FiniteProbability.expectation (torusRCPMF hN hM q)
    (fun A => T.indicator (fun _ => (1 : ℝ))
      (FK.configurationSplitEquiv (fullDiamondGraph hN hM) R
        (torusRCConfigurationEquiv hN hM hN4 hM4 A))) = _
  rw [torusRCPMF_expectation_split hN hM hN4 hM4 q R]
  apply congrArg (FK.FiniteProbability.expectation _)
  funext H
  by_cases hH : H ∈ S
  · simp only [Set.indicator_of_mem hH, torusRCFiberEventProbability]
    apply congrArg (FK.FiniteProbability.expectation _)
    funext A
    simp [T, Set.indicator, hH]
  · simp only [Set.indicator_of_notMem hH]
    have hz : (fun A : FK.RemainingConfiguration (fullDiamondGraph hN hM) R =>
        T.indicator (fun _ => (1 : ℝ)) (A, H)) = fun _ => 0 := by
      funext A
      simp [T, Set.indicator, hH]
    rw [hz, FK.FiniteProbability.expectation_const]

/-- A uniform conditional-fiber bound survives conditioning on any event
determined by the frozen edges. No association of that exterior event is needed. -/
theorem torusRCProbability_fiber_lower_bound (hN : Even N) (hM : Even M)
    (hN4 : 4 ≤ N) (hM4 : 4 ≤ M) (q : Set.Ici (1 : ℝ))
    (R : FK.Configuration (fullDiamondGraph hN hM))
    (S : Set (FK.RemovedConfiguration (fullDiamondGraph hN hM) R))
    (E : FK.RemovedConfiguration (fullDiamondGraph hN hM) R →
      Set (FK.RemainingConfiguration (fullDiamondGraph hN hM) R))
    (c : ℝ) (hc : ∀ H ∈ S, c ≤ torusRCFiberEventProbability
      (torusRCFiberLaw hN hM hN4 hM4 q R H) (E H)) :
    c * torusRCProbability hN hM q {A |
      (FK.configurationSplitEquiv (fullDiamondGraph hN hM) R
        (torusRCConfigurationEquiv hN hM hN4 hM4 A)).2 ∈ S} ≤
    torusRCProbability hN hM q {A |
      let P := FK.configurationSplitEquiv (fullDiamondGraph hN hM) R
        (torusRCConfigurationEquiv hN hM hN4 hM4 A)
      P.2 ∈ S ∧ P.1 ∈ E P.2} := by
  classical
  have hout := torusRCProbability_split_event hN hM hN4 hM4 q R S (fun _ => Set.univ)
  simp only [Set.mem_univ, and_true] at hout
  simp only [torusRCFiberEventProbability, Set.indicator_univ,
    FK.FiniteProbability.expectation_const] at hout
  rw [hout, torusRCProbability_split_event hN hM hN4 hM4 q R S E,
    FK.FiniteProbability.expectation, FK.FiniteProbability.expectation, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro H _
  by_cases hH : H ∈ S
  · simp only [Set.indicator_of_mem hH, mul_one]
    rw [mul_comm c]
    exact mul_le_mul_of_nonneg_left (hc H hH) ENNReal.toReal_nonneg
  · simp [Set.indicator_of_notMem hH]

end

end PottsDiscontinuity.TorusRC
