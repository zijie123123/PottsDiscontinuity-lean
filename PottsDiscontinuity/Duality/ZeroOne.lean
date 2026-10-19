module

public import PottsDiscontinuity.Duality.Decay

/-!
# The conditional zero–one step

This module only upgrades positive origin percolation to almost-sure existence
of an infinite cluster, given a zero–one law for the existence event. Neither
positive origin percolation nor the zero–one law is established here.
-/

@[expose] public section

open MeasureTheory

namespace PottsDiscontinuity.Duality

lemma infiniteClusterAt_subset_existsInfiniteCluster (v : ℤ × ℤ) :
    infiniteClusterAt v ⊆ existsInfiniteCluster := by
  intro ω hω
  exact ⟨v, hω⟩

/-- The ergodicity-dependent last step, with its zero–one input explicit.
This is not the exponential-decay-to-wired-positivity implication. -/
theorem existsInfiniteCluster_eq_one_of_zero_one
    (μ : Measure FK.LatticeConfiguration) (v : ℤ × ℤ)
    (hpos : 0 < μ (infiniteClusterAt v))
    (hzero_one : μ existsInfiniteCluster = 0 ∨ μ existsInfiniteCluster = 1) :
    μ existsInfiniteCluster = 1 := by
  rcases hzero_one with hzero | hone
  · have hle := measure_mono (μ := μ) (infiniteClusterAt_subset_existsInfiniteCluster v)
    rw [hzero] at hle
    exact False.elim (not_lt_of_ge hle hpos)
  · exact hone

end PottsDiscontinuity.Duality
