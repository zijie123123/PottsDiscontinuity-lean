/- Adapted from an earlier, unpublished formalization of the planar FK model by the same author.
Parameter generalization: independent 0 < p < 1 and 1 ≤ q, with no upper bound on q. -/
module

public import PottsDiscontinuity.FK.CylinderDetermination
public import Mathlib.Topology.Order.MonotoneConvergence
public import Mathlib.Topology.Separation.Hausdorff

/-!
# Weak convergence from monotone finite cylinders

On the compact whole-lattice configuration space, monotonicity of every finite
all-open cylinder probability forces weak convergence of the probability laws.
-/

@[expose] public section

namespace PottsDiscontinuity.FK

open Set MeasureTheory Filter Topology
noncomputable section


/-- The coordinate map recording every finite all-open cylinder probability. -/
def cylinderProbabilityCoordinates (μ : ProbabilityMeasure LatticeConfiguration) :
    Finset squareLattice.edgeSet → NNReal :=
  fun F => μ (LatticeConfiguration.allOpen F)

theorem continuous_cylinderProbabilityCoordinates :
    Continuous cylinderProbabilityCoordinates := by
  refine continuous_pi fun F => ?_
  rw [continuous_iff_continuousAt]
  intro μ
  exact LatticeConfiguration.tendsto_allOpen_of_weak tendsto_id F

/-- If every finite all-open cylinder probability is monotone along a sequence,
then the sequence converges weakly to a unique probability measure. -/
theorem probabilityMeasures_tendsto_of_monotone_allOpen
    {μs : ℕ → ProbabilityMeasure LatticeConfiguration}
    (hmono : ∀ F : Finset squareLattice.edgeSet,
      Monotone (fun n => μs n (LatticeConfiguration.allOpen F))) :
    ∃! μ : ProbabilityMeasure LatticeConfiguration, Tendsto μs atTop (𝓝 μ) := by
  obtain ⟨μ, φ, hφ, hweak⟩ := CompactSpace.tendsto_subseq μs
  have hlimit (F : Finset squareLattice.edgeSet) :
      μ (LatticeConfiguration.allOpen F) =
        ⨆ n, μs n (LatticeConfiguration.allOpen F) := by
    let f : ℕ → NNReal := fun n => μs n (LatticeConfiguration.allOpen F)
    have hf : Monotone f := hmono F
    have hbounded : BddAbove (Set.range f) := by
      refine ⟨1, ?_⟩
      rintro x ⟨n, rfl⟩
      exact ProbabilityMeasure.apply_le_one (μs n) (LatticeConfiguration.allOpen F)
    have ht := tendsto_atTop_ciSup hf hbounded
    have hsub := ht.comp hφ.tendsto_atTop
    have hweakF := LatticeConfiguration.tendsto_allOpen_of_weak hweak F
    exact tendsto_nhds_unique hweakF hsub
  let κ := cylinderProbabilityCoordinates
  have hκcont : Continuous κ := continuous_cylinderProbabilityCoordinates
  have hκinj : Function.Injective κ := by
    intro μ₁ μ₂ h
    apply LatticeConfiguration.probabilityMeasure_eq_of_allOpen
    intro F
    exact congrFun h F
  have hκembed : IsClosedEmbedding κ := hκcont.isClosedEmbedding hκinj
  have hκtendsto : Tendsto (fun n => κ (μs n)) atTop (𝓝 (κ μ)) := by
    apply tendsto_pi_nhds.2
    intro F
    let f : ℕ → NNReal := fun n => μs n (LatticeConfiguration.allOpen F)
    have hf : Monotone f := hmono F
    have hbounded : BddAbove (Set.range f) := by
      refine ⟨1, ?_⟩
      rintro x ⟨n, rfl⟩
      exact ProbabilityMeasure.apply_le_one (μs n) (LatticeConfiguration.allOpen F)
    have ht := tendsto_atTop_ciSup hf hbounded
    change Tendsto f atTop (𝓝 (μ (LatticeConfiguration.allOpen F)))
    rw [hlimit F]
    exact ht
  have hfull : Tendsto μs atTop (𝓝 μ) := hκembed.tendsto_nhds_iff.mpr hκtendsto
  refine ⟨μ, hfull, ?_⟩
  intro ν hν
  exact tendsto_nhds_unique hν hfull

end
end PottsDiscontinuity.FK
