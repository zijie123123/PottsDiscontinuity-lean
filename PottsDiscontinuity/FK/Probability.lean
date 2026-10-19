/- Adapted from an earlier, unpublished formalization of the planar FK model by the same author.
Parameter generalization: independent 0 < p < 1 and 1 ≤ q, with no upper bound on q. -/
module

public import Mathlib.Probability.ProbabilityMassFunction.Constructions

/-!
# Normalizing strictly positive weights on a finite configuration space

This module supplies the elementary normalization used in equation (1.2) of the
source paper. Its hypotheses will be discharged for the concrete FK weights in the
model module; it does not assume any percolation estimate.
-/

@[expose] public section

namespace PottsDiscontinuity.FK.FiniteProbability

open scoped BigOperators

variable {α : Type*} [Fintype α]

/-- The finite sum of configuration weights. -/
noncomputable def partition (w : α → ℝ) : ℝ := ∑ a, w a

theorem partition_pos [Nonempty α] (w : α → ℝ) (hw : ∀ a, 0 < w a) :
    0 < partition w := by
  exact Finset.sum_pos (fun a _ => hw a) Finset.univ_nonempty

/-- The normalized weight of a strictly positive finite family. -/
noncomputable def probability [Nonempty α] (w : α → ℝ)
    (_hw : ∀ a, 0 < w a) (a : α) : ℝ :=
  w a / partition w

theorem probability_pos [Nonempty α] (w : α → ℝ) (hw : ∀ a, 0 < w a) (a : α) :
    0 < probability w hw a :=
  div_pos (hw a) (partition_pos w hw)

theorem sum_probability [Nonempty α] (w : α → ℝ) (hw : ∀ a, 0 < w a) :
    ∑ a, probability w hw a = 1 := by
  unfold probability
  rw [← Finset.sum_div]
  exact div_self (ne_of_gt (partition_pos w hw))

theorem sum_ofReal_probability [Nonempty α] (w : α → ℝ) (hw : ∀ a, 0 < w a) :
    ∑ a, ENNReal.ofReal (probability w hw a) = 1 := by
  rw [← ENNReal.ofReal_sum_of_nonneg (fun a _ => (probability_pos w hw a).le)]
  rw [sum_probability, ENNReal.ofReal_one]

/-- The probability mass function with the prescribed positive weights. -/
noncomputable def pmf [Nonempty α] (w : α → ℝ) (hw : ∀ a, 0 < w a) : PMF α :=
  PMF.ofFintype (fun a => ENNReal.ofReal (probability w hw a))
    (sum_ofReal_probability w hw)

theorem pmf_apply [Nonempty α] (w : α → ℝ) (hw : ∀ a, 0 < w a) (a : α) :
    pmf w hw a = ENNReal.ofReal (w a / partition w) := rfl

theorem pmf_pos [Nonempty α] (w : α → ℝ) (hw : ∀ a, 0 < w a) (a : α) :
    0 < pmf w hw a := by
  rw [pmf_apply, ENNReal.ofReal_pos]
  exact div_pos (hw a) (partition_pos w hw)

end PottsDiscontinuity.FK.FiniteProbability
