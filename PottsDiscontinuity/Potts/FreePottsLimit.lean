module

public import PottsDiscontinuity.Potts.FreeCylinderPartition
public import PottsDiscontinuity.Potts.ESCylinderLaw
public import PottsDiscontinuity.Potts.SpinObservation
public import PottsDiscontinuity.Potts.PottsLimitConstruction

/-! Free Potts box limits and their Edwards–Sokal colouring identification. -/

@[expose] public section

namespace PottsDiscontinuity.Potts

open Classical MeasureTheory Filter Topology
noncomputable section

local instance freeLimitVertexDecidableEq (V : Finset (ℤ × ℤ)) :
    DecidableEq ↥(V : Set (ℤ × ℤ)) := fun _ _ => Classical.propDecidable _
local instance freeLimitVertexFintype (V : Finset (ℤ × ℤ)) :
    Fintype ↥(V : Set (ℤ × ℤ)) := Fintype.ofFinite _
local instance freeLimitEdgeDecidableEq (V : Finset (ℤ × ℤ)) :
    DecidableEq (squareLattice.induce (V : Set (ℤ × ℤ))).edgeSet := fun _ _ => Classical.propDecidable _
local instance freeLimitEdgeFintype (V : Finset (ℤ × ℤ)) :
    Fintype (squareLattice.induce (V : Set (ℤ × ℤ))).edgeSet := Fintype.ofFinite _

theorem free_potts_cylinder_tendsto (q : ℕ) (hq : 2 ≤ q) (β : ℝ) (hβ : 0 < β)
    (φ : ProbabilityMeasure FK.LatticeConfiguration)
    (hφ : Tendsto (fun n => FK.boxProbabilityMeasure (fkParameters q hq β hβ) (0, 0) n) atTop (𝓝 φ))
    (A : Finset (ℤ × ℤ)) (ξ : SpinSpace q) :
    Tendsto (fun n => (pottsBoxProbabilityMeasure q hq β hβ 0 n).toMeasure.real (spinCylinder q A ξ))
      atTop (𝓝 (freeESCylinder q φ.toMeasure A ξ)) := by
  have ht := free_partitionExpectation_tendsto (fkParameters q hq β hβ) φ hφ
    (fun a : ↥A => a.val) (fun R => clusterCylinderProbability R id (fun a : ↥A => ξ a.val))
  change Tendsto _ atTop (𝓝 (freeESCylinder q φ.toMeasure A ξ)) at ht
  apply ht.congr'
  have hs : ∀ᶠ n : ℕ in atTop, A ⊆ box n :=
    (eventually_all_finset A).mpr (fun x _ => FK.eventually_mem_box x)
  filter_upwards [hs] with n hn
  rw [← spinObservationEvent_subtype q A ξ]
  exact ((pottsBoxProbabilityMeasure_observed q hq β hβ 0 n (fun a : ↥A => a.val)
    (fun a => hn a.property) (fun a : ↥A => ξ a.val)).trans
    (potts_free_cylinder_eq_partitionExpectation q hq β hβ n (fun a : ↥A => a.val)
      (fun a => hn a.property) (fun a : ↥A => ξ a.val))).symm

/-- An actual free RC box limit and an actual free Potts box limit, with the
law of every Potts cylinder given by independent uniform cluster colouring. -/
theorem exists_free_potts_limit_with_colouring (q : ℕ) (hq : 2 ≤ q) (β : ℝ) (hβ : 0 < β) :
    ∃ (φ : ProbabilityMeasure FK.LatticeConfiguration) (μ : ProbabilityMeasure (SpinSpace q)),
      IsRCInfiniteVolumeLimit (fkParameters q hq β hβ).toP (fkParameters q hq β hβ).toQ 0 φ.toMeasure ∧
      IsPottsInfiniteVolumeLimit q β 0 μ.toMeasure ∧
      IsFreeEdwardsSokalColouring q φ.toMeasure μ.toMeasure := by
  obtain ⟨φ, hφ, _⟩ := FK.Internal.freeBoxLimit_existsUnique (q := fkParameters q hq β hβ)
  have hw := hφ (fun _ => (0, 0)) (fun n => n)
    FK.origin_latticeBox_nested FK.origin_latticeBox_exhaustive
  obtain ⟨μ, hμ, hcyl⟩ := potts_limit_of_cylinder_limits q hq β hβ 0
    (freeESCylinder q φ.toMeasure) (free_potts_cylinder_tendsto q hq β hβ φ hw)
  exact ⟨φ, μ, FK.isRCInfiniteVolumeLimit_of_freeBox_tendsto _ φ hw, hμ, μ.prop, hcyl⟩

end
end PottsDiscontinuity.Potts
