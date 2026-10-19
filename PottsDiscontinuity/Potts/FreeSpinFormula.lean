module

public import PottsDiscontinuity.Potts.FreeSpinObservations
public import PottsDiscontinuity.Potts.SpinKernels
public import PottsDiscontinuity.Potts.PartitionExpectationAlgebra
public import PottsDiscontinuity.Potts.InfinitePartitionMeasurability
public import PottsDiscontinuity.Potts.SpinEventDecomposition

/-! Corrected consequence 3: the free spin correlation and actual RC connectivity. -/

@[expose] public section

namespace PottsDiscontinuity.Potts

open Classical MeasureTheory Filter Topology
noncomputable section

/-- The corrected free two-spin formula, including coincident vertices. The
RC law is the free box limit at `p = 1 - exp (-β)`. -/
theorem free_spin_correlation (q : ℕ) (hq : 2 ≤ q) (β : ℝ) (hβ : 0 < β)
    (φ : ProbabilityMeasure FK.LatticeConfiguration)
    (hφ : Tendsto (fun n => FK.boxProbabilityMeasure (fkParameters q hq β hβ) (0, 0) n) atTop (𝓝 φ))
    (μ : ProbabilityMeasure (SpinSpace q)) (hμ : IsPottsInfiniteVolumeLimit q β 0 μ.toMeasure)
    (x y : ℤ × ℤ) :
    μ.toMeasure.real {σ | σ x = σ y} =
      1 / (q : ℝ) + (1 - 1 / (q : ℝ)) *
        φ.toMeasure.real {ω | (rcInfiniteOpenGraph ω).Reachable x y} := by
  let v : Bool → ℤ × ℤ := fun b => if b then y else x
  have hp (c : Set.Icc 1 q) : μ.toMeasure.real {σ | σ x = c ∧ σ y = c} =
      ((q : ℝ) ^ 2)⁻¹ + ((q : ℝ)⁻¹ - ((q : ℝ) ^ 2)⁻¹) *
        φ.toMeasure.real {ω | (rcInfiniteOpenGraph ω).Reachable x y} := by
    have he : {σ : SpinSpace q | σ x = c ∧ σ y = c} = spinObservationEvent q v (fun _ => c) := by
      ext σ
      simp [spinObservationEvent, v]
    rw [he, free_spin_observation_formula q hq β hβ φ hφ μ hμ v (fun _ => c)]
    have hk : (fun R : Setoid Bool => clusterCylinderProbability R id (fun _ => c)) =
        fun R => ((q : ℝ) ^ 2)⁻¹ + ((q : ℝ)⁻¹ - ((q : ℝ) ^ 2)⁻¹) *
          (if R false true then 1 else 0) := by
      funext R
      rw [free_two_point_kernel]
      by_cases h : R false true <;> simp only [h, ite_true, ite_false] <;> ring
    rw [hk, partitionExpectation_affine_indicator φ.toMeasure (infiniteFreePartition v)
      (infiniteFreePartition_measurableSet v)]
    rfl
  rw [measureReal_same_colour_sum μ.toMeasure (fun σ : SpinSpace q => σ x) (fun σ => σ y)
    (measurable_pi_apply x) (measurable_pi_apply y)]
  simp_rw [hp]
  rw [Finset.sum_const, Finset.card_univ, ← Nat.card_eq_fintype_card, card_pottsColors, nsmul_eq_mul]
  have hq0 : (q : ℝ) ≠ 0 := by exact_mod_cast (show q ≠ 0 by omega)
  field_simp

end
end PottsDiscontinuity.Potts
