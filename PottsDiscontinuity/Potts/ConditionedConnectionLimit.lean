module

public import PottsDiscontinuity.Potts.ConditionedOuterLaw
public import PottsDiscontinuity.Potts.ConditionedEventLimits
public import PottsDiscontinuity.Potts.WiredConnectionLimit

/-! Merged connection-data limits survive the literal corner correction. -/

@[expose] public section

namespace PottsDiscontinuity.Potts

open Classical MeasureTheory Filter Topology
noncomputable section

 theorem iInter_wiredDataEvent_succ (F : Finset (Option (ℤ × ℤ) × Option (ℤ × ℤ))) :
    (⋂ n, wiredDataEvent (n + 1) F) = infiniteMergedDataEvent F := by
  rw [← iInter_wiredDataEvent F]
  apply Set.Subset.antisymm
  · intro ω hω
    simp only [Set.mem_iInter] at hω ⊢
    intro n
    exact wiredDataEvent_antitone F (Nat.le_succ n) (hω n)
  · intro ω hω
    simp only [Set.mem_iInter] at hω ⊢
    exact fun n => hω (n + 1)

/-- Positive moments of the full marked connection data under the actual
conditioned outer law converge to the merged infinite wired data. -/
theorem conditioned_connection_moments_tendsto
    (q : ℕ) (hq : 2 ≤ q) (β : ℝ) (hβ : 0 < β)
    (μ : ProbabilityMeasure FK.LatticeConfiguration)
    (hμ : Tendsto (fun n => FK.wiredBoxProbabilityMeasure (fkParameters q hq β hβ) (0, 0) n)
      atTop (𝓝 μ)) (F : Finset (Option (ℤ × ℤ) × Option (ℤ × ℤ))) :
    Tendsto (fun n => (conditionedOuterBoxProbabilityMeasure (fkParameters q hq β hβ) n).toMeasure.real
      (wiredDataEvent (n + 1) F)) atTop (𝓝 (μ.toMeasure.real (infiniteMergedDataEvent F))) := by
  let θ := fkParameters q hq β hβ
  have hν := conditionedOuterBox_tendsto q hq β hβ μ hμ
  have hweak : Tendsto (fun n => openBoxProbabilityMeasure θ (n + 1)) atTop (𝓝 μ) := by
    simpa only [openBoxProbabilityMeasure_eq_wired, Function.comp_def, θ] using hμ.comp (tendsto_add_atTop_nat 1)
  rw [← iInter_wiredDataEvent_succ F]
  apply decreasing_event_limit_of_density (fun n => openBoxProbabilityMeasure θ (n + 1))
    (conditionedOuterBoxProbabilityMeasure θ) μ (fun n => wiredDataEvent (n + 1) F)
    ((wiredDataEvent_antitone F).comp_monotone (fun _ _ h => Nat.add_le_add_right h 1))
    (fun n => (wiredDataEvent_isClopen (n + 1) F).isOpen.measurableSet)
    ((1 - FK.edgeParameter θ) ^ 4) (pow_pos (FK.one_sub_edgeParameter_pos θ) 4)
  · filter_upwards [eventually_gt_atTop 0] with n hn S hS
    exact conditionedOuterBox_density θ n hn S hS
  · intro m
    have ht := ProbabilityMeasure.tendsto_measure_of_isClopen_of_tendsto hweak
      (wiredDataEvent_isClopen (m + 1) F)
    simpa only [ProbabilityMeasure.measureReal_eq_coe_coeFn, Function.comp_def] using
      NNReal.continuous_coe.continuousAt.tendsto.comp ht
  · intro m
    have ht := ProbabilityMeasure.tendsto_measure_of_isClopen_of_tendsto hν
      (wiredDataEvent_isClopen (m + 1) F)
    simpa only [ProbabilityMeasure.measureReal_eq_coe_coeFn, Function.comp_def] using
      NNReal.continuous_coe.continuousAt.tendsto.comp ht
  · rw [iInter_wiredDataEvent_succ]
    exact (wired_connection_moments_tendsto θ μ hμ F).comp (tendsto_add_atTop_nat 1)

end
end PottsDiscontinuity.Potts
