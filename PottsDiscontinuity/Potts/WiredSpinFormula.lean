module

public import PottsDiscontinuity.Potts.WiredSpinObservations
public import PottsDiscontinuity.Potts.SpinKernels
public import PottsDiscontinuity.Potts.PartitionExpectationAlgebra
public import PottsDiscontinuity.Potts.InfinitePartitionMeasurability

/-! Corrected consequence 2: the boundary-colour probability and wired percolation. -/

@[expose] public section

namespace PottsDiscontinuity.Potts

open Classical MeasureTheory Filter Topology
noncomputable section

/-- The corrected `(1 - 1/q)` coefficient, for any observed vertex. The RC law
is the wired box limit at `p = 1 - exp (-β)`. -/
theorem wired_spin_probability (q : ℕ) (hq : 2 ≤ q) (β : ℝ) (hβ : 0 < β)
    (i : Fin (q + 1)) (hi : 1 ≤ (i : ℕ))
    (φ : ProbabilityMeasure FK.LatticeConfiguration)
    (hφ : Tendsto (fun n => FK.wiredBoxProbabilityMeasure (fkParameters q hq β hβ) (0, 0) n) atTop (𝓝 φ))
    (μ : ProbabilityMeasure (SpinSpace q)) (hμ : IsPottsInfiniteVolumeLimit q β i μ.toMeasure)
    (x : ℤ × ℤ) :
    μ.toMeasure.real {σ | (σ x : ℕ) = (i : ℕ)} =
      1 / (q : ℝ) + (1 - 1 / (q : ℝ)) *
        φ.toMeasure.real {ω | clusterIsInfinite (rcInfiniteOpenGraph ω) x} := by
  let v : Unit → ℤ × ℤ := fun _ => x
  let c := boundaryColor q i hi
  have he : {σ : SpinSpace q | (σ x : ℕ) = (i : ℕ)} = spinObservationEvent q v (fun _ => c) := by
    ext σ
    simp [spinObservationEvent, v, c, boundaryColor, Subtype.ext_iff]
  rw [he, wired_spin_observation_formula q hq β hβ i hi φ hφ μ hμ v (fun _ => c)]
  have hk : (fun R : Setoid (Option Unit) => pinnedClusterCylinderProbability R some (fun _ => c) none c) =
      fun R => (q : ℝ)⁻¹ + (1 - (q : ℝ)⁻¹) * (if R (some PUnit.unit) none then 1 else 0) := by
    funext R
    rw [wired_one_point_kernel]
    by_cases h : R (some PUnit.unit) none <;> simp only [h, ite_true, ite_false] <;> ring
  change partitionExpectation φ.toMeasure (infiniteWiredPartition (Option.map v))
    (fun R => pinnedClusterCylinderProbability R some (fun _ => c) none c) = _
  rw [hk, partitionExpectation_affine_indicator φ.toMeasure (infiniteWiredPartition (Option.map v))
    (infiniteWiredPartition_measurableSet (Option.map v))]
  have hE : {ω | infiniteWiredPartition (Option.map v) ω (some PUnit.unit) none} =
      {ω | clusterIsInfinite (rcInfiniteOpenGraph ω) x} := by
    ext ω
    change infiniteMergedSetoid (rcInfiniteOpenGraph ω) (some x) none ↔ _
    exact infiniteMergedSetoid_some_none _ _
  rw [hE]
  simp only [one_div]

/-- The origin-spin version of corrected consequence 2 in Theorem 3.19. -/
theorem wired_origin_spin_probability (q : ℕ) (hq : 2 ≤ q) (β : ℝ) (hβ : 0 < β)
    (i : Fin (q + 1)) (hi : 1 ≤ (i : ℕ))
    (φ : ProbabilityMeasure FK.LatticeConfiguration)
    (hφ : Tendsto (fun n => FK.wiredBoxProbabilityMeasure (fkParameters q hq β hβ) (0, 0) n) atTop (𝓝 φ))
    (μ : ProbabilityMeasure (SpinSpace q)) (hμ : IsPottsInfiniteVolumeLimit q β i μ.toMeasure) :
    μ.toMeasure.real {σ | (σ (0, 0) : ℕ) = (i : ℕ)} =
      1 / (q : ℝ) + (1 - 1 / (q : ℝ)) *
        φ.toMeasure.real {ω | clusterIsInfinite (rcInfiniteOpenGraph ω) (0, 0)} :=
  wired_spin_probability q hq β hβ i hi φ hφ μ hμ (0, 0)

end
end PottsDiscontinuity.Potts
