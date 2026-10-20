module

public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Basic.Real.Basic
public import Mathlib.Combinatorics.SetFamily.FourFunctions
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Data.Setoid.Basic
public import Mathlib.MeasureTheory.Measure.Real
public import Mathlib.Order.Interval.Set.Basic
public import Mathlib.Probability.ProbabilityMassFunction.Constructions
public import Mathlib.SetTheory.Cardinal.Finite

/-! Finite conditional probabilities and exterior-event decomposition. -/

@[expose] public section

namespace PottsDiscontinuity.Potts

open MeasureTheory Classical
noncomputable section

variable {E D : Type*} [Fintype E] [Fintype D]
local instance finiteConditioningMeasurable : MeasurableSpace E := ⊤
local instance finiteConditioningDiscrete : DiscreteMeasurableSpace E := ⟨fun _ => trivial⟩

theorem finite_filter_measure (p : PMF E) (B S : Set E)
    (h : ∃ a ∈ B, a ∈ p.support) :
    (p.filter B h).toMeasure S = p.toMeasure (S ∩ B) / p.toMeasure B := by
  classical
  have ht (a : E) : S.indicator (p.filter B h) a =
      (S ∩ B).indicator p a * (∑' b, B.indicator p b)⁻¹ := by
    by_cases hS : a ∈ S <;> by_cases hB : a ∈ B <;>
      simp [Set.indicator, PMF.filter_apply, hS, hB]
  rw [PMF.toMeasure_apply_fintype]
  simp_rw [ht]
  rw [← Finset.sum_mul, PMF.toMeasure_apply_fintype, PMF.toMeasure_apply_fintype,
    tsum_fintype, div_eq_mul_inv]

theorem finite_filter_measureReal (p : PMF E) (B S : Set E)
    (h : ∃ a ∈ B, a ∈ p.support) :
    (p.filter B h).toMeasure.real S = p.toMeasure.real (S ∩ B) / p.toMeasure.real B := by
  rw [Measure.real, finite_filter_measure, ENNReal.toReal_div]
  rfl

/-- Partitioning a finite probability by the value of a random variable. -/
theorem finite_measure_fibers (p : PMF E) (r : E → D) (S : Set E) (T : Set D) :
    p.toMeasure.real {e | e ∈ S ∧ r e ∈ T} =
      ∑ d : D, if d ∈ T then p.toMeasure.real (S ∩ {e | r e = d}) else 0 := by
  classical
  have h (U : Set E) : p.toMeasure.real U =
      ∑ e : E, if e ∈ U then (p e).toReal else 0 := by
    rw [Measure.real, PMF.toMeasure_apply_fintype, ENNReal.toReal_sum]
    · apply Finset.sum_congr rfl
      intro e _
      by_cases he : e ∈ U <;> simp [Set.indicator, he]
    · intro e _
      by_cases he : e ∈ U <;> simp [Set.indicator, he, p.apply_ne_top]
  simp_rw [h]
  trans ∑ d : D, ∑ e : E,
    if d ∈ T then (if e ∈ S ∩ {e | r e = d} then (p e).toReal else 0) else 0
  · rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro e _
    symm
    rw [Finset.sum_eq_single (r e)]
    · by_cases he : e ∈ S <;> by_cases ht : r e ∈ T <;> simp [he, ht]
    · intro d _ hd
      simp [Ne.symm hd]
    · simp
  · apply Finset.sum_congr rfl
    intro d _
    by_cases hd : d ∈ T <;> simp [hd]

end
end PottsDiscontinuity.Potts
