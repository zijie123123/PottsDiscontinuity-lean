module

public import PottsDiscontinuity.Potts.CylinderColoring
public import PottsDiscontinuity.Potts.LimitCompactness
public import PottsDiscontinuity.Potts.ObservedPartitionLimits

/-! Edwards–Sokal infinite-colouring laws characterized on every finite cylinder.
The kernels are the independent uniform component-colouring kernels. In the
wired case the ghost class contains all infinite clusters and has fixed colour. -/

@[expose] public section

namespace PottsDiscontinuity.Potts

open MeasureTheory
noncomputable section

/-- The cylinder probability of independent uniform colouring of actual free components. -/
def freeESCylinder (q : ℕ) (φ : Measure FK.LatticeConfiguration)
    (A : Finset (ℤ × ℤ)) (ξ : SpinSpace q) : ℝ :=
  partitionExpectation φ (infiniteFreePartition (fun a : ↥A => a.val))
    (fun R => clusterCylinderProbability R id (fun a : ↥A => ξ a.val))

/-- The cylinder probability with every infinite wired component coloured `i`
and all finite components independently uniform. -/
def wiredESCylinder (q : ℕ) (φ : Measure FK.LatticeConfiguration)
    (i : Fin (q + 1)) (hi : 1 ≤ (i : ℕ)) (A : Finset (ℤ × ℤ)) (ξ : SpinSpace q) : ℝ :=
  partitionExpectation φ (infiniteWiredPartition (Option.map (fun a : ↥A => a.val)))
    (fun R => pinnedClusterCylinderProbability R some (fun a : ↥A => ξ a.val) none (boundaryColor q i hi))

/-- Equality on all finite cylinders with independent uniform colouring of the free RC components. -/
def IsFreeEdwardsSokalColouring (q : ℕ) (φ : Measure FK.LatticeConfiguration)
    (μ : Measure (SpinSpace q)) : Prop :=
  IsProbabilityMeasure μ ∧ ∀ A ξ, μ.real (spinCylinder q A ξ) = freeESCylinder q φ A ξ

/-- Equality on all finite cylinders with finite components uniformly coloured
and all infinite components in the single ghost class coloured `i`. -/
def IsWiredEdwardsSokalColouring (q : ℕ) (φ : Measure FK.LatticeConfiguration)
    (i : Fin (q + 1)) (hi : 1 ≤ (i : ℕ)) (μ : Measure (SpinSpace q)) : Prop :=
  IsProbabilityMeasure μ ∧ ∀ A ξ, μ.real (spinCylinder q A ξ) = wiredESCylinder q φ i hi A ξ

end
end PottsDiscontinuity.Potts
