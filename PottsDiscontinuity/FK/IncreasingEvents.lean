/- Adapted from an earlier, unpublished formalization of the planar FK model by the same author.
Parameter generalization: independent 0 < p < 1 and 1 ≤ q, with no upper bound on q. -/
module

public import PottsDiscontinuity.FK.BoundaryComparison
public import PottsDiscontinuity.FK.PositiveAssociation

/-!
# FKG and wiring comparison for actual increasing events

The finite sums are identified with the real-valued probabilities of the
existing full power-set FK measure. In particular the correlation inequality
and wiring comparison below are statements about that measure itself.
-/

@[expose] public section

namespace PottsDiscontinuity.FK

open scoped BigOperators
noncomputable section

variable {V : Type*} [Finite V] {G : SimpleGraph V}
local instance increasingEventsEdgeFintype : Fintype G.edgeSet := Fintype.ofFinite _
local instance increasingEventsEdgeDecidableEq : DecidableEq G.edgeSet := Classical.decEq _

theorem measure_toReal_eq_indicator_sum (q : Parameters) (ξ : BoundaryCondition V)
    (s : Set (Configuration G)) :
    (measure G q ξ s).toReal =
      ∑ A, configurationProbability G q ξ A * s.indicator (fun _ => (1 : ℝ)) A := by
  classical
  rw [measure_apply, ENNReal.toReal_sum]
  · apply Finset.sum_congr rfl
    intro A hA
    by_cases h : A ∈ s
    · simp [Set.indicator, h, law_apply,
        ENNReal.toReal_ofReal (configurationProbability_pos G q ξ A).le]
    · simp [Set.indicator, h]
  · intro A hA
    by_cases h : A ∈ s
    · simpa [Set.indicator, h] using (law G q ξ).apply_ne_top A
    · simp [Set.indicator, h]

omit [Finite V] in
private theorem event_indicator_nonneg (s : Set (Configuration G)) :
    ∀ A, 0 ≤ s.indicator (fun _ => (1 : ℝ)) A := by
  classical
  intro A
  by_cases h : A ∈ s <;> simp [Set.indicator, h]

omit [Finite V] in
private theorem event_indicator_monotone (s : Set (Configuration G)) (hs : IsUpperSet s) :
    Monotone (s.indicator (fun _ => (1 : ℝ))) := by
  classical
  intro A B hAB
  by_cases hA : A ∈ s
  · have hB := hs hAB hA
    simp [Set.indicator, hA, hB]
  · simp only [Set.indicator_of_notMem hA]
    exact event_indicator_nonneg s B

/-- Any two increasing events are positively correlated under the actual FK measure. -/
theorem measure_positive_association (q : Parameters) (ξ : BoundaryCondition V)
    (s t : Set (Configuration G)) (hs : IsUpperSet s) (ht : IsUpperSet t) :
    (measure G q ξ s).toReal * (measure G q ξ t).toReal ≤
      (measure G q ξ (s ∩ t)).toReal := by
  classical
  have h := configurationProbability_positive_association q ξ
    (s.indicator fun _ => (1 : ℝ)) (t.indicator fun _ => (1 : ℝ))
    (event_indicator_nonneg s) (event_indicator_nonneg t)
    (event_indicator_monotone s hs) (event_indicator_monotone t ht)
  have hi (A : Configuration G) :
      s.indicator (fun _ => (1 : ℝ)) A * t.indicator (fun _ => (1 : ℝ)) A =
        (s ∩ t).indicator (fun _ => (1 : ℝ)) A := by
    by_cases hsA : A ∈ s <;> by_cases htA : A ∈ t <;>
      simp [Set.indicator, hsA, htA]
  simp_rw [hi] at h
  simpa only [measure_toReal_eq_indicator_sum] using h

/-- Increasing event probabilities increase when boundary identifications are added. -/
theorem measure_boundary_comparison (q : Parameters) (ξ η : BoundaryCondition V)
    (hξη : ξ.partition ≤ η.partition) (s : Set (Configuration G)) (hs : IsUpperSet s) :
    (measure G q ξ s).toReal ≤ (measure G q η s).toReal := by
  have h := configurationProbability_boundary_comparison q ξ η hξη
    (s.indicator fun _ => (1 : ℝ)) (event_indicator_nonneg s) (event_indicator_monotone s hs)
  simpa only [measure_toReal_eq_indicator_sum, mul_comm] using h

end
end PottsDiscontinuity.FK
