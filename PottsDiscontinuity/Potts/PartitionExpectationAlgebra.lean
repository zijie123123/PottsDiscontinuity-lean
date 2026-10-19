module

public import PottsDiscontinuity.Potts.FinitePartitionLimits

/-! Expectations of the affine connection indicators in the spin identities. -/

@[expose] public section

namespace PottsDiscontinuity.Potts

open Classical MeasureTheory
noncomputable section
variable {A X : Type*} [Finite A] [MeasurableSpace X]
local instance algebraSetoidFintype : Fintype (Setoid A) := Fintype.ofFinite _

theorem sum_partition_mass (μ : Measure X) [IsProbabilityMeasure μ] (r : X → Setoid A)
    (hr : ∀ R, MeasurableSet {x | r x = R}) :
    ∑ R : Setoid A, μ.real {x | r x = R} = 1 := by
  have hs := sum_measureReal_preimage_singleton (μ := μ) (f := r) Finset.univ
    (fun R _ => hr R)
  have he (R : Setoid A) : r ⁻¹' {R} = {x | r x = R} := by ext x; simp
  simp_rw [he] at hs
  simpa using hs

theorem sum_partition_mass_indicator (μ : Measure X) [IsProbabilityMeasure μ]
    (r : X → Setoid A) (hr : ∀ R, MeasurableSet {x | r x = R}) (P : Setoid A → Prop) :
    (∑ R : Setoid A, if P R then μ.real {x | r x = R} else 0) = μ.real {x | P (r x)} := by
  rw [← Finset.sum_filter]
  have hs := sum_measureReal_preimage_singleton (μ := μ) (f := r) (Finset.univ.filter P)
    (fun R _ => hr R)
  have he : r ⁻¹' (↑(Finset.univ.filter P) : Set (Setoid A)) = {x | P (r x)} := by ext x; simp
  rw [he] at hs
  exact hs

/-- Average a corrected spin kernel over its exact finite connection partition. -/
theorem partitionExpectation_affine_indicator (μ : Measure X) [IsProbabilityMeasure μ]
    (r : X → Setoid A) (hr : ∀ R, MeasurableSet {x | r x = R})
    (P : Setoid A → Prop) (a b : ℝ) :
    partitionExpectation μ r (fun R => a + b * (if P R then 1 else 0)) =
      a + b * μ.real {x | P (r x)} := by
  unfold partitionExpectation
  have ht (R : Setoid A) : μ.real {x | r x = R} * (a + b * (if P R then 1 else 0)) =
      a * μ.real {x | r x = R} + b * (if P R then μ.real {x | r x = R} else 0) := by
    by_cases h : P R <;> simp only [h, ite_true, ite_false] <;> ring
  simp_rw [ht]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
    sum_partition_mass μ r hr, sum_partition_mass_indicator μ r hr P]
  ring

end
end PottsDiscontinuity.Potts
