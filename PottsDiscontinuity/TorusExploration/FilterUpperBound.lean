module

public import Mathlib.Probability.ProbabilityMassFunction.Constructions
public import PottsDiscontinuity.FK.Expectation

/-! A joint event is bounded by its genuine conditional probability. -/

@[expose] public section

namespace PottsDiscontinuity.TorusExploration
open FK.FiniteProbability
noncomputable section
open scoped Classical
variable {α : Type*} [Fintype α]

lemma pmf_le_filter_of_mem (p : PMF α) (T : Set α)
    (hT : ∃ a ∈ T, a ∈ p.support) (a : α) (ha : a ∈ T) : p a ≤ p.filter T hT a := by
  rw [PMF.filter_apply,Set.indicator_of_mem ha]
  have hden : (∑' b, T.indicator p b) ≤ 1 := by
    rw [← p.tsum_coe]
    apply ENNReal.tsum_le_tsum
    intro b
    by_cases hb : b ∈ T <;> simp [hb]
  have hinv : (1 : ENNReal) ≤ (∑' b, T.indicator p b)⁻¹ := by
    simpa using ENNReal.inv_le_inv.mpr hden
  simpa only [mul_one] using mul_le_mul' (le_refl (p a)) hinv

/-- No independence is asserted: conditioning divides by a probability ≤1. -/
theorem joint_expectation_le_filter (p : PMF α) (T E : Set α)
    (hT : ∃ a ∈ T, a ∈ p.support) :
    expectation p ((T ∩ E).indicator fun _ => (1 : ℝ)) ≤
      expectation (p.filter T hT) (E.indicator fun _ => (1 : ℝ)) := by
  apply Finset.sum_le_sum
  intro a _
  by_cases ha : a ∈ T
  · by_cases he : a ∈ E
    · simp only [Set.indicator_of_mem (show a ∈ T ∩ E from ⟨ha,he⟩),Set.indicator_of_mem he,mul_one]
      exact ENNReal.toReal_mono ((p.filter T hT).apply_ne_top a) (pmf_le_filter_of_mem p T hT a ha)
    · simp [he]
  · simp only [Set.indicator_of_notMem (show a ∉ T ∩ E from fun h => ha h.1),mul_zero]
    by_cases he : a ∈ E
    · rw [Set.indicator_of_mem he,mul_one]
      exact ENNReal.toReal_nonneg
    · simp only [Set.indicator_of_notMem he,mul_zero,le_refl]

end
end PottsDiscontinuity.TorusExploration
